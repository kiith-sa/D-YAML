
//          Copyright Ferdinand Majerech 2011-2014.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

/// YAML scanner.
/// Code based on PyYAML: http://www.pyyaml.org
module dyaml.scanner;


import core.stdc.string;

import std.algorithm;
import std.array;
import std.conv;
import std.ascii : isAlphaNum, isDigit, isHexDigit;
import std.exception;
import std.range;
import std.string;
import std.typecons;
import std.traits : Unqual;
import std.utf;

import dyaml.escapes;
import dyaml.exception;
import dyaml.queue;
import dyaml.reader;
import dyaml.style;
import dyaml.token;

package:
/// Scanner produces tokens of the following types:
/// STREAM-START
/// STREAM-END
/// DIRECTIVE(name, value)
/// DOCUMENT-START
/// DOCUMENT-END
/// BLOCK-SEQUENCE-START
/// BLOCK-MAPPING-START
/// BLOCK-END
/// FLOW-SEQUENCE-START
/// FLOW-MAPPING-START
/// FLOW-SEQUENCE-END
/// FLOW-MAPPING-END
/// BLOCK-ENTRY
/// FLOW-ENTRY
/// KEY
/// VALUE
/// ALIAS(value)
/// ANCHOR(value)
/// TAG(value)
/// SCALAR(value, plain, style)

alias isBreak = among!('\n', '\r', '\u0085', '\u2028', '\u2029');

alias isBreakOrSpace = among!(' ', '\n', '\r', '\u0085', '\u2028', '\u2029');

alias isWhiteSpace = among!(' ', '\t', '\n', '\r', '\u0085', '\u2028', '\u2029');

alias isNonLinebreakWhitespace = among!(' ', '\t');

alias isNonScalarStartCharacter = among!('-', '?', ':', ',', '[', ']', '{', '}',
    '#', '&', '*', '!', '|', '>', '\'', '"', '%', '@', '`', ' ', '\t', '\n',
    '\r', '\u0085', '\u2028', '\u2029');

alias uriChar = AliasSeq!('-', ';', '/', '?', ':', '@', '&', '=', '+', '$', ',',
    '_', '.', '!', '~', '*', '\'', '(', ')', '[', ']', '%');
alias isURIChar = among!(uriChar);

alias nsChar = AliasSeq!(' ', '\n', '\r', '\u0085', '\u2028', '\u2029');
alias isNSChar = among!(nsChar);

alias isBChar = among!('\n', '\r', '\u0085', '\u2028', '\u2029');

alias isFlowScalarBreakSpace = among!(' ', '\t', '\n', '\r', '\u0085', '\u2028', '\u2029', '\'', '"', '\\');

alias isFlowIndicator = among!(',', '[', ']', '{', '}');

/// 80 is a common upper limit for line width.
enum expectedLineLength = 80;

/// Marked exception thrown at scanner errors.
///
/// See_Also: MarkedYAMLException
class ScannerException : MarkedYAMLException
{
    mixin MarkedExceptionCtors;
}

/// Generates tokens from data provided by a Reader.
struct Scanner
{
    private:
        /// A simple key is a key that is not denoted by the '?' indicator.
        /// For example:
        ///   ---
        ///   block simple key: value
        ///   ? not a simple key:
        ///   : { flow simple key: value }
        /// We emit the KEY token before all keys, so when we find a potential simple
        /// key, we try to locate the corresponding ':' indicator. Simple keys should be
        /// limited to a single line and 1024 characters.
        ///
        /// 16 bytes on 64-bit.
        static struct SimpleKey
        {
            /// Character index in reader where the key starts.
            uint charIndex = uint.max;
            /// Index of the key token from start (first token scanned being 0).
            uint tokenIndex;
            /// Line the key starts at.
            uint line;
            /// Column the key starts at.
            ushort column;
            /// Is this required to be a simple key?
            bool required;
            /// Is this struct "null" (invalid)?.
            bool isNull;
        }

        /// Block chomping types.
        enum Chomping
        {
            /// Strip all trailing line breaks. '-' indicator.
            strip,
            /// Line break of the last line is preserved, others discarded. Default.
            clip,
            /// All trailing line breaks are preserved. '+' indicator.
            keep
        }

        /// Reader used to read from a file/stream.
        Reader reader_;
        /// Are we done scanning?
        bool done_;

        /// Level of nesting in flow context. If 0, we're in block context.
        uint flowLevel_;
        /// Current indentation level.
        int indent_ = -1;
        /// Past indentation levels. Used as a stack.
        Appender!(int[]) indents_;

        /// Processed tokens not yet emitted. Used as a queue.
        Queue!Token tokens_;

        /// Number of tokens emitted through the getToken method.
        uint tokensTaken_;

        /// Can a simple key start at the current position? A simple key may start:
        /// - at the beginning of the line, not counting indentation spaces
        ///       (in block context),
        /// - after '{', '[', ',' (in the flow context),
        /// - after '?', ':', '-' (in the block context).
        /// In the block context, this flag also signifies if a block collection
        /// may start at the current position.
        bool allowSimpleKey_ = true;

        /// Possible simple keys indexed by flow levels.
        SimpleKey[] possibleSimpleKeys_;

    public:
        /// Construct a Scanner using specified Reader.
        this(Reader reader) @safe nothrow
        {
            // Return the next token, but do not delete it from the queue
            reader_   = reader;
            fetchStreamStart();
        }

        /// Advance to the next token
        void popFront() @safe
        {
            ++tokensTaken_;
            tokens_.pop();
        }

        /// Return the current token
        const(Token) front() @safe
        {
            enforce(!empty, "No token left to peek");
            return tokens_.peek();
        }

        /// Return whether there are any more tokens left.
        bool empty() @safe
        {
            while (needMoreTokens())
            {
                fetchToken();
            }
            return tokens_.empty;
        }

    private:
        /// Most scanning error messages have the same format; so build them with this
        /// function.
        string expected(T)(string expected, T found)
        {
            return text("expected ", expected, ", but found ", found);
        }

        /// Determine whether or not we need to fetch more tokens before peeking/getting a token.
        bool needMoreTokens() @safe pure
        {
            if(done_)         { return false; }
            if(tokens_.empty) { return true; }

            /// The current token may be a potential simple key, so we need to look further.
            stalePossibleSimpleKeys();
            return nextPossibleSimpleKey() == tokensTaken_;
        }

        /// Fetch at token, adding it to tokens_.
        void fetchToken() @safe
        {
            // Eat whitespaces and comments until we reach the next token.
            skipToNextToken();

            // Remove obsolete possible simple keys.
            stalePossibleSimpleKeys();

            // Compare current indentation and column. It may add some tokens
            // and decrease the current indentation level.
            unwindIndent(reader_.column);

            // End of stream
            if(reader_.empty) { return fetchStreamEnd(); }

            // Get the next character.
            const dchar c = reader_.front;

            // Fetch the token.
            if(checkDirective())     { return fetchDirective();     }
            if(checkDocumentStart()) { return fetchDocumentStart(); }
            if(checkDocumentEnd())   { return fetchDocumentEnd();   }
            // Order of the following checks is NOT significant.
            switch(c)
            {
                case '[':  return fetchFlowSequenceStart();
                case '{':  return fetchFlowMappingStart();
                case ']':  return fetchFlowSequenceEnd();
                case '}':  return fetchFlowMappingEnd();
                case ',':  return fetchFlowEntry();
                case '!':  return fetchTag();
                case '\'': return fetchSingle();
                case '\"': return fetchDouble();
                case '*':  return fetchAlias();
                case '&':  return fetchAnchor();
                case '?':  if(checkKey())        { return fetchKey();        } goto default;
                case ':':  if(checkValue())      { return fetchValue();      } goto default;
                case '-':  if(checkBlockEntry()) { return fetchBlockEntry(); } goto default;
                case '|':  if(flowLevel_ == 0)   { return fetchLiteral();    } break;
                case '>':  if(flowLevel_ == 0)   { return fetchFolded();     } break;
                default:   if(checkPlain())      { return fetchPlain();      }
            }

            throw new ScannerException("While scanning for the next token, found character " ~
                                       "\'%s\', index %s that cannot start any token"
                                       .format(c, to!int(c)), reader_.mark);
        }


        /// Return the token number of the nearest possible simple key.
        uint nextPossibleSimpleKey() @safe pure nothrow @nogc
        {
            uint minTokenNumber = uint.max;
            foreach(k, ref simpleKey; possibleSimpleKeys_)
            {
                if(simpleKey.isNull) { continue; }
                minTokenNumber = min(minTokenNumber, simpleKey.tokenIndex);
            }
            return minTokenNumber;
        }

        /// Remove entries that are no longer possible simple keys.
        ///
        /// According to the YAML specification, simple keys
        /// - should be limited to a single line,
        /// - should be no longer than 1024 characters.
        /// Disabling this will allow simple keys of any length and
        /// height (may cause problems if indentation is broken though).
        void stalePossibleSimpleKeys() @safe pure
        {
            foreach(level, ref key; possibleSimpleKeys_)
            {
                if(key.isNull) { continue; }
                if(key.line != reader_.line || reader_.charIndex - key.charIndex > 1024)
                {
                    enforce(!key.required,
                            new ScannerException("While scanning a simple key",
                                                 Mark(key.line, key.column),
                                                 "could not find expected ':'", reader_.mark));
                    key.isNull = true;
                }
            }
        }

        /// Check if the next token starts a possible simple key and if so, save its position.
        ///
        /// This function is called for ALIAS, ANCHOR, TAG, SCALAR(flow), '[', and '{'.
        void savePossibleSimpleKey() @safe pure
        {
            // Check if a simple key is required at the current position.
            const required = (flowLevel_ == 0 && indent_ == reader_.column);
            assert(allowSimpleKey_ || !required, "A simple key is required only if it is " ~
                   "the first token in the current line. Therefore it is always allowed.");

            if(!allowSimpleKey_) { return; }

            // The next token might be a simple key, so save its number and position.
            removePossibleSimpleKey();
            const tokenCount = tokensTaken_ + cast(uint)tokens_.length;

            const line   = reader_.line;
            const column = reader_.column;
            const key    = SimpleKey(cast(uint)reader_.charIndex, tokenCount, line,
                                     cast(ushort)min(column, ushort.max), required);

            if(possibleSimpleKeys_.length <= flowLevel_)
            {
                const oldLength = possibleSimpleKeys_.length;
                possibleSimpleKeys_.length = flowLevel_ + 1;
                //No need to initialize the last element, it's already done in the next line.
                possibleSimpleKeys_[oldLength .. flowLevel_] = SimpleKey.init;
            }
            possibleSimpleKeys_[flowLevel_] = key;
        }

        /// Remove the saved possible key position at the current flow level.
        void removePossibleSimpleKey() @safe pure
        {
            if(possibleSimpleKeys_.length <= flowLevel_) { return; }

            if(!possibleSimpleKeys_[flowLevel_].isNull)
            {
                const key = possibleSimpleKeys_[flowLevel_];
                enforce(!key.required,
                        new ScannerException("While scanning a simple key",
                                             Mark(key.line, key.column),
                                             "could not find expected ':'", reader_.mark));
                possibleSimpleKeys_[flowLevel_].isNull = true;
            }
        }

        /// Decrease indentation, removing entries in indents_.
        ///
        /// Params:  column = Current column in the file/stream.
        void unwindIndent(const int column) @safe
        {
            if(flowLevel_ > 0)
            {
                // In flow context, tokens should respect indentation.
                // The condition should be `indent >= column` according to the spec.
                // But this condition will prohibit intuitively correct
                // constructions such as
                // key : {
                // }

                // In the flow context, indentation is ignored. We make the scanner less
                // restrictive than what the specification requires.
                // if(pedantic_ && flowLevel_ > 0 && indent_ > column)
                // {
                //     throw new ScannerException("Invalid intendation or unclosed '[' or '{'",
                //                                reader_.mark)
                // }
                return;
            }

            // In block context, we may need to issue the BLOCK-END tokens.
            while(indent_ > column)
            {
                indent_ = indents_.data.back;
                assert(indents_.data.length);
                indents_.shrinkTo(indents_.data.length - 1);
                tokens_.push(blockEndToken(reader_.mark, reader_.mark));
            }
        }

        /// Increase indentation if needed.
        ///
        /// Params:  column = Current column in the file/stream.
        ///
        /// Returns: true if the indentation was increased, false otherwise.
        bool addIndent(int column) @safe
        {
            if(indent_ >= column){return false;}
            indents_ ~= indent_;
            indent_ = column;
            return true;
        }


        /// Add STREAM-START token.
        void fetchStreamStart() @safe nothrow
        {
            tokens_.push(streamStartToken(reader_.mark, reader_.mark));
        }

        ///Add STREAM-END token.
        void fetchStreamEnd() @safe
        {
            //Set intendation to -1 .
            unwindIndent(-1);
            removePossibleSimpleKey();
            allowSimpleKey_ = false;
            possibleSimpleKeys_.destroy;

            tokens_.push(streamEndToken(reader_.mark, reader_.mark));
            done_ = true;
        }

        /// Add DIRECTIVE token.
        void fetchDirective() @safe
        {
            // Set intendation to -1 .
            unwindIndent(-1);
            // Reset simple keys.
            removePossibleSimpleKey();
            allowSimpleKey_ = false;

            auto directive = scanDirective();
            tokens_.push(directive);
        }

        /// Add DOCUMENT-START or DOCUMENT-END token.
        void fetchDocumentIndicator(TokenID id)()
            if(id == TokenID.documentStart || id == TokenID.documentEnd)
        {
            // Set indentation to -1 .
            unwindIndent(-1);
            // Reset simple keys. Note that there can't be a block collection after '---'.
            removePossibleSimpleKey();
            allowSimpleKey_ = false;

            Mark startMark = reader_.mark;
            reader_.popFrontN(3);
            tokens_.push(simpleToken!id(startMark, reader_.mark));
        }

        /// Aliases to add DOCUMENT-START or DOCUMENT-END token.
        alias fetchDocumentStart = fetchDocumentIndicator!(TokenID.documentStart);
        alias fetchDocumentEnd = fetchDocumentIndicator!(TokenID.documentEnd);

        /// Add FLOW-SEQUENCE-START or FLOW-MAPPING-START token.
        void fetchFlowCollectionStart(TokenID id)() @safe
        {
            // '[' and '{' may start a simple key.
            savePossibleSimpleKey();
            // Simple keys are allowed after '[' and '{'.
            allowSimpleKey_ = true;
            ++flowLevel_;

            Mark startMark = reader_.mark;
            reader_.popFront();
            tokens_.push(simpleToken!id(startMark, reader_.mark));
        }

        /// Aliases to add FLOW-SEQUENCE-START or FLOW-MAPPING-START token.
        alias fetchFlowSequenceStart = fetchFlowCollectionStart!(TokenID.flowSequenceStart);
        alias fetchFlowMappingStart = fetchFlowCollectionStart!(TokenID.flowMappingStart);

        /// Add FLOW-SEQUENCE-START or FLOW-MAPPING-START token.
        void fetchFlowCollectionEnd(TokenID id)()
        {
            // Reset possible simple key on the current level.
            removePossibleSimpleKey();
            // No simple keys after ']' and '}'.
            allowSimpleKey_ = false;
            --flowLevel_;

            Mark startMark = reader_.mark;
            reader_.popFront();
            tokens_.push(simpleToken!id(startMark, reader_.mark));
        }

        /// Aliases to add FLOW-SEQUENCE-START or FLOW-MAPPING-START token/
        alias fetchFlowSequenceEnd = fetchFlowCollectionEnd!(TokenID.flowSequenceEnd);
        alias fetchFlowMappingEnd = fetchFlowCollectionEnd!(TokenID.flowMappingEnd);

        /// Add FLOW-ENTRY token;
        void fetchFlowEntry() @safe
        {
            // Reset possible simple key on the current level.
            removePossibleSimpleKey();
            // Simple keys are allowed after ','.
            allowSimpleKey_ = true;

            Mark startMark = reader_.mark;
            reader_.popFront();
            tokens_.push(flowEntryToken(startMark, reader_.mark));
        }

        /// Additional checks used in block context in fetchBlockEntry and fetchKey.
        ///
        /// Params:  type = String representing the token type we might need to add.
        ///          id   = Token type we might need to add.
        void blockChecks(string type, TokenID id)()
        {
            enum context = type ~ " keys are not allowed here";
            // Are we allowed to start a key (not neccesarily a simple one)?
            enforce(allowSimpleKey_, new ScannerException(context, reader_.mark));

            if(addIndent(reader_.column))
            {
                tokens_.push(simpleToken!id(reader_.mark, reader_.mark));
            }
        }

        /// Add BLOCK-ENTRY token. Might add BLOCK-SEQUENCE-START in the process.
        void fetchBlockEntry() @safe
        {
            if(flowLevel_ == 0) { blockChecks!("Sequence", TokenID.blockSequenceStart)(); }

            // It's an error for the block entry to occur in the flow context,
            // but we let the parser detect this.

            // Reset possible simple key on the current level.
            removePossibleSimpleKey();
            // Simple keys are allowed after '-'.
            allowSimpleKey_ = true;

            Mark startMark = reader_.mark;
            reader_.popFront();
            tokens_.push(blockEntryToken(startMark, reader_.mark));
        }

        /// Add KEY token. Might add BLOCK-MAPPING-START in the process.
        void fetchKey() @safe
        {
            if(flowLevel_ == 0) { blockChecks!("Mapping", TokenID.blockMappingStart)(); }

            // Reset possible simple key on the current level.
            removePossibleSimpleKey();
            // Simple keys are allowed after '?' in the block context.
            allowSimpleKey_ = (flowLevel_ == 0);

            Mark startMark = reader_.mark;
            reader_.popFront();
            tokens_.push(keyToken(startMark, reader_.mark));
        }

        /// Add VALUE token. Might add KEY and/or BLOCK-MAPPING-START in the process.
        void fetchValue() @safe
        {
            //Do we determine a simple key?
            if(possibleSimpleKeys_.length > flowLevel_ &&
               !possibleSimpleKeys_[flowLevel_].isNull)
            {
                const key = possibleSimpleKeys_[flowLevel_];
                possibleSimpleKeys_[flowLevel_].isNull = true;
                Mark keyMark = Mark(key.line, key.column);
                const idx = key.tokenIndex - tokensTaken_;

                assert(idx >= 0);

                // Add KEY.
                // Manually inserting since tokens are immutable (need linked list).
                tokens_.insert(keyToken(keyMark, keyMark), idx);

                // If this key starts a new block mapping, we need to add BLOCK-MAPPING-START.
                if(flowLevel_ == 0 && addIndent(key.column))
                {
                    tokens_.insert(blockMappingStartToken(keyMark, keyMark), idx);
                }

                // There cannot be two simple keys in a row.
                allowSimpleKey_ = false;
            }
            // Part of a complex key
            else
            {
                // We can start a complex value if and only if we can start a simple key.
                enforce(flowLevel_ > 0 || allowSimpleKey_,
                        new ScannerException("Mapping values are not allowed here", reader_.mark));

                // If this value starts a new block mapping, we need to add
                // BLOCK-MAPPING-START. It'll be detected as an error later by the parser.
                if(flowLevel_ == 0 && addIndent(reader_.column))
                {
                    tokens_.push(blockMappingStartToken(reader_.mark, reader_.mark));
                }

                // Reset possible simple key on the current level.
                removePossibleSimpleKey();
                // Simple keys are allowed after ':' in the block context.
                allowSimpleKey_ = (flowLevel_ == 0);
            }

            // Add VALUE.
            Mark startMark = reader_.mark;
            reader_.popFront();
            tokens_.push(valueToken(startMark, reader_.mark));
        }

        /// Add ALIAS or ANCHOR token.
        void fetchAnchor_(TokenID id)() @safe
            if(id == TokenID.alias_ || id == TokenID.anchor)
        {
            // ALIAS/ANCHOR could be a simple key.
            savePossibleSimpleKey();
            // No simple keys after ALIAS/ANCHOR.
            allowSimpleKey_ = false;

            auto anchor = scanAnchor(id);
            tokens_.push(anchor);
        }

        /// Aliases to add ALIAS or ANCHOR token.
        alias fetchAlias = fetchAnchor_!(TokenID.alias_);
        alias fetchAnchor = fetchAnchor_!(TokenID.anchor);

        /// Add TAG token.
        void fetchTag() @safe
        {
            //TAG could start a simple key.
            savePossibleSimpleKey();
            //No simple keys after TAG.
            allowSimpleKey_ = false;

            tokens_.push(scanTag());
        }

        /// Add block SCALAR token.
        void fetchBlockScalar(ScalarStyle style)() @safe
            if(style == ScalarStyle.literal || style == ScalarStyle.folded)
        {
            // Reset possible simple key on the current level.
            removePossibleSimpleKey();
            // A simple key may follow a block scalar.
            allowSimpleKey_ = true;

            auto blockScalar = scanBlockScalar(style);
            tokens_.push(blockScalar);
        }

        /// Aliases to add literal or folded block scalar.
        alias fetchLiteral = fetchBlockScalar!(ScalarStyle.literal);
        alias fetchFolded = fetchBlockScalar!(ScalarStyle.folded);

        /// Add quoted flow SCALAR token.
        void fetchFlowScalar(ScalarStyle quotes)()
        {
            // A flow scalar could be a simple key.
            savePossibleSimpleKey();
            // No simple keys after flow scalars.
            allowSimpleKey_ = false;

            // Scan and add SCALAR.
            auto scalar = scanFlowScalar(quotes);
            tokens_.push(scalar);
        }

        /// Aliases to add single or double quoted block scalar.
        alias fetchSingle = fetchFlowScalar!(ScalarStyle.singleQuoted);
        alias fetchDouble = fetchFlowScalar!(ScalarStyle.doubleQuoted);

        /// Add plain SCALAR token.
        void fetchPlain() @safe
        {
            // A plain scalar could be a simple key
            savePossibleSimpleKey();
            // No simple keys after plain scalars. But note that scanPlain() will
            // change this flag if the scan is finished at the beginning of the line.
            allowSimpleKey_ = false;
            auto plain = scanPlain();

            // Scan and add SCALAR. May change allowSimpleKey_
            tokens_.push(plain);
        }

    pure:

        ///Check if the next token is DIRECTIVE:        ^ '%' ...
        bool checkDirective() @safe
        {
            return reader_.front == '%' && reader_.column == 0;
        }

        /// Check if the next token is DOCUMENT-START:   ^ '---' (' '|'\n')
        bool checkDocumentStart() @safe
        {
                if (reader_.empty || (reader_.column != 0))
                {
                    return false;
                }
                if (reader_.length >= 4)
                {
                    const slice = reader_[0 .. 4];
                    return (slice.startsWith("---") && slice[$ - 1].isWhiteSpace);
                }
                return false;
        }

        /// Check if the next token is DOCUMENT-END:     ^ '...' (' '|'\n'|EOF)
        bool checkDocumentEnd() @safe
        {
                if (reader_.empty || (reader_.column != 0))
                {
                    return false;
                }
                if (reader_.length >= 4)
                {
                    const slice = reader_[0 .. 4];
                    return (slice.startsWith("...") && slice[$ - 1].isWhiteSpace);
                }
                // ...<EOF>
                return reader_.length == 3 && (reader_[0 .. 3] == "...");
        }

        /// Check if the next token is BLOCK-ENTRY:      '-' (' '|'\n')
        bool checkBlockEntry() @safe
        {
            if (reader_.length >= 2)
            {
                const slice = reader_[0 .. 2];
                return (slice[0] == '-' && slice[$ - 1].isWhiteSpace);
            }
            return false;
        }

        /// Check if the next token is KEY(flow context):    '?'
        ///
        /// or KEY(block context):   '?' (' '|'\n')
        bool checkKey() @safe
        {
            if (reader_.length >= 2)
            {
                const slice = reader_[0 .. 2];
                return (slice[0] == '?' && slice[$ - 1].isWhiteSpace);
            }
            return flowLevel_ > 0;
        }

        /// Check if the next token is VALUE(flow context):  ':'
        ///
        /// or VALUE(block context): ':' (' '|'\n')
        bool checkValue() @safe
        {
            return (flowLevel_ > 0) ||
                ((reader_.length >= 2) && (reader_[1].isWhiteSpace));
        }

        /// Check if the next token is a plain scalar.
        ///
        /// A plain scalar may start with any non-space character except:
        ///   '-', '?', ':', ',', '[', ']', '{', '}',
        ///   '#', '&', '*', '!', '|', '>', '\'', '\"',
        ///   '%', '@', '`'.
        ///
        /// It may also start with
        ///   '-', '?', ':'
        /// if it is followed by a non-space character.
        ///
        /// Note that we limit the last rule to the block context (except the
        /// '-' character) because we want the flow context to be space
        /// independent.
        bool checkPlain() @safe pure
        {
            const c = reader_.front;
            if(!c.isNonScalarStartCharacter)
            {
                return true;
            }
            return ((reader_.length >= 2) && !reader_[1].isWhiteSpace) &&
                   (c == '-' || (flowLevel_ == 0 && (c == '?' || c == ':')));
        }

        /// Move to the next non-space character.
        void findNextNonSpace() @safe
        {
            reader_.popUntil!(x => x != ' ');
        }

        /// Scan a string of alphanumeric or "-_" characters.
        void scanAlphaNumericToSlice(string name)(const Mark startMark, ref string buf)
        {
            auto slice = reader_.getSliceUntil!(x => !x.isAlphaNum && !x.among!('-', '_'));
            enforce(slice.length > 0, new ScannerException("While scanning " ~ name,
                startMark, expected("alphanumeric, '-' or '_'", reader_.front), reader_.mark));
            buf ~= slice;
        }

        /// Scan and throw away all characters until next line break.
        void scanToNextBreak() @safe
        {
            reader_.popUntil!(x => x.isBreak);
        }

        /// Scan all characters until next line break.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        auto scanToNextBreakToSlice() @safe
        {
            return reader_.getSliceUntil!(x => cast(bool)x.isBreak);
        }


        /// Move to next token in the file/stream.
        ///
        /// We ignore spaces, line breaks and comments.
        /// If we find a line break in the block context, we set
        /// allowSimpleKey` on.
        ///
        /// We do not yet support BOM inside the stream as the
        /// specification requires. Any such mark will be considered as a part
        /// of the document.
        void skipToNextToken() @safe
        {
            // TODO(PyYAML): We need to make tab handling rules more sane. A good rule is:
            //   Tabs cannot precede tokens
            //   BLOCK-SEQUENCE-START, BLOCK-MAPPING-START, BLOCK-END,
            //   KEY(block), VALUE(block), BLOCK-ENTRY
            // So the checking code is
            //   if <TAB>:
            //       allowSimpleKey_ = false
            // We also need to add the check for `allowSimpleKey_ == true` to
            // `unwindIndent` before issuing BLOCK-END.
            // Scanners for block, flow, and plain scalars need to be modified.

            for(;;)
            {
                //All whitespace in flow context is ignored, even whitespace
                // not allowed in other contexts
                if (flowLevel_ > 0)
                {
                    while(!reader_.empty && reader_.front.isNonLinebreakWhitespace) { reader_.popFront; }
                }
                else
                {
                    findNextNonSpace();
                }
                if (reader_.empty)
                {
                    break;
                }
                if(reader_.front == '#') { scanToNextBreak(); }
                if(scanLineBreak() != '\0')
                {
                    if(flowLevel_ == 0) { allowSimpleKey_ = true; }
                }
                else
                {
                    break;
                }
            }
        }

        /// Scan directive token.
        Token scanDirective() @safe
        {
            Mark startMark = reader_.mark;
            // Skip the '%'.
            reader_.popFront();

            // Scan directive name
            const name = scanDirectiveNameToSlice(startMark);

            string value;

            // Index where tag handle ends and suffix starts in a tag directive value.
            uint tagHandleEnd = uint.max;
            if(name == "YAML")     { value = scanYAMLDirectiveValueToSlice(startMark); }
            else if(name == "TAG") { value = scanTagDirectiveValueToSlice(startMark, tagHandleEnd); }

            Mark endMark = reader_.mark;

            DirectiveType directive;
            if(name == "YAML")     { directive = DirectiveType.yaml; }
            else if(name == "TAG") { directive = DirectiveType.tag; }
            else
            {
                directive = DirectiveType.reserved;
                scanToNextBreak();
            }

            scanDirectiveIgnoredLine(startMark);

            return directiveToken(startMark, endMark, value, directive, tagHandleEnd);
        }

        /// Scan name of a directive token.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanDirectiveNameToSlice(const Mark startMark) @safe
        {
            // Scan directive name.
            string result;
            // Reserve a reasonable number of characters.
            result.reserve(expectedLineLength);
            scanAlphaNumericToSlice!"a directive"(startMark, result);

            enforce(reader_.front.isBreakOrSpace,
                new ScannerException("While scanning a directive", startMark,
                    expected("alphanumeric, '-' or '_'", reader_.front), reader_.mark));
            return result;
        }

        /// Scan value of a YAML directive token. Returns major, minor version separated by '.'.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanYAMLDirectiveValueToSlice(const Mark startMark) @safe
        {
            string buf;
            findNextNonSpace();

            buf ~= scanYAMLDirectiveNumberToSlice(startMark);

            enforce(reader_.front == '.',
                new ScannerException("While scanning a directive", startMark,
                    expected("digit or '.'", reader_.front), reader_.mark));
            // Skip the '.'.
            reader_.popFront();

            buf ~= '.';
            buf ~= scanYAMLDirectiveNumberToSlice(startMark);

            enforce(reader_.front.isBreakOrSpace,
                new ScannerException("While scanning a directive", startMark,
                    expected("digit or '.'", reader_.front), reader_.mark));
            return buf;
        }

        /// Scan a number from a YAML directive.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        auto scanYAMLDirectiveNumberToSlice(const Mark startMark) @safe
        {
            enforce(isDigit(reader_.front),
                new ScannerException("While scanning a directive", startMark,
                    expected("digit", reader_.front), reader_.mark));
            return reader_.getSliceUntil!(x => !x.isDigit);
        }

        /// Scan value of a tag directive.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        ///
        /// Returns: Length of tag handle (which is before tag prefix) in scanned data
        string scanTagDirectiveValueToSlice(const Mark startMark, out uint handleLength) @safe
        {
            string result;
            findNextNonSpace();
            result ~= scanTagDirectiveHandleToSlice(startMark);
            handleLength = cast(uint)result.length;
            findNextNonSpace();
            result ~= scanTagDirectivePrefixToSlice(startMark);
            return result;
        }

        /// Scan handle of a tag directive.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanTagDirectiveHandleToSlice(const Mark startMark) @safe
        {
            auto buf = scanTagHandleToSlice!"directive"(startMark);
            enforce(reader_.front == ' ',
                new ScannerException("While scanning a directive handle", startMark,
                    expected("' '", reader_.front), reader_.mark));
            return buf;
        }

        /// Scan prefix of a tag directive.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanTagDirectivePrefixToSlice(const Mark startMark) @safe
        {
            auto buf = scanTagURIToSlice!"directive"(startMark);
            enforce(reader_.front.isBreakOrSpace,
                new ScannerException("While scanning a directive prefix", startMark,
                    expected("' '", reader_.front), reader_.mark));
            return buf;
        }

        /// Scan (and ignore) ignored line after a directive.
        void scanDirectiveIgnoredLine(const Mark startMark) @safe
        {
            findNextNonSpace();
            if(reader_.front == '#') { scanToNextBreak(); }
            enforce(reader_.front.isBreak,
                new ScannerException("While scanning a directive", startMark,
                      expected("comment or a line break", reader_.front), reader_.mark));
            scanLineBreak();
        }


        /// Scan an alias or an anchor.
        ///
        /// The specification does not restrict characters for anchors and
        /// aliases. This may lead to problems, for instance, the document:
        ///   [ *alias, value ]
        /// can be interpteted in two ways, as
        ///   [ "value" ]
        /// and
        ///   [ *alias , "value" ]
        /// Therefore we restrict aliases to ASCII alphanumeric characters.
        Token scanAnchor(const TokenID id) @safe
        {
            const startMark = reader_.mark;
            const dchar i = reader_.front;
            reader_.popFront();

            string value;
            if(i == '*') { scanAlphaNumericToSlice!"an alias"(startMark, value); }
            else         { scanAlphaNumericToSlice!"an anchor"(startMark, value); }

            enum anchorCtx = "While scanning an anchor";
            enum aliasCtx  = "While scanning an alias";
            enforce(reader_.front.isWhiteSpace ||
                reader_.front.among!('?', ':', ',', ']', '}', '%', '@'),
                new ScannerException(i == '*' ? aliasCtx : anchorCtx, startMark,
                    expected("alphanumeric, '-' or '_'", reader_.front), reader_.mark));

            if(id == TokenID.alias_)
            {
                return aliasToken(startMark, reader_.mark, value);
            }
            if(id == TokenID.anchor)
            {
                return anchorToken(startMark, reader_.mark, value);
            }
            assert(false, "This code should never be reached");
        }

        /// Scan a tag token.
        Token scanTag() @safe
        {
            string slice;
            const startMark = reader_.mark;
            auto copy = reader_[1 .. $];
            dchar c = copy.front;

            // Index where tag handle ends and tag suffix starts in the tag value
            // (slice) we will produce.
            uint handleEnd;

            if(c == '<')
            {
                reader_.popFront();
                reader_.popFront();

                handleEnd = 0;
                slice ~= scanTagURIToSlice!"tag"(startMark);
                enforce(reader_.front == '>',
                    new ScannerException("While scanning a tag", startMark,
                        expected("'>'", reader_.front), reader_.mark));
                reader_.popFront();
            }
            else if(c.isWhiteSpace)
            {
                reader_.popFront();
                handleEnd = 0;
                slice ~= '!';
            }
            else
            {
                uint length = 1;
                bool useHandle;

                while(!copy.front.isBreakOrSpace)
                {
                    if(copy.front == '!')
                    {
                        useHandle = true;
                        break;
                    }
                    copy.popFront();
                }

                if(useHandle)
                {
                    slice ~= scanTagHandleToSlice!"tag"(startMark);
                    handleEnd = cast(uint)slice.length;
                }
                else
                {
                    reader_.popFront();
                    slice ~= '!';
                    handleEnd = cast(uint)slice.length;
                }

                slice ~= scanTagURIToSlice!"tag"(startMark);
            }

            enforce(reader_.front.isBreakOrSpace,
                new ScannerException("While scanning a tag", startMark, expected("' '", reader_.front),
                    reader_.mark));

            return tagToken(startMark, reader_.mark, slice, handleEnd);
        }

        /// Scan a block scalar token with specified style.
        Token scanBlockScalar(const ScalarStyle style) @safe
        {
            const startMark = reader_.mark;

            // Scan the header.
            reader_.popFront();

            const indicators = scanBlockScalarIndicators(startMark);

            const chomping   = indicators[0];
            const increment  = indicators[1];
            skipBlockScalarIgnoredLine(startMark);

            // Determine the indentation level and go to the first non-empty line.
            Mark endMark;
            uint indent = max(1, indent_ + 1);

            string slice;
            string buf;
            if(increment == int.min)
            {
                uint indentation;
                buf ~= scanBlockScalarIndentationToSlice(indentation, endMark);
                indent  = max(indent, indentation);
            }
            else
            {
                indent += increment - 1;
                scanBlockScalarBreaksToSlice(indent, buf, endMark);
            }

            // int.max means there's no line break (int.max is outside UTF-32).
            dchar lineBreak = cast(dchar)int.max;

            // Scan the inner part of the block scalar.
            while(reader_.column == indent && !reader_.empty)
            {
                slice ~= buf;
                const bool leadingNonSpace = !reader_.front.among!(' ', '\t');
                // This is where the 'interesting' non-whitespace data gets read.
                slice ~= scanToNextBreakToSlice();
                lineBreak = scanLineBreak();


                // This transaction serves to rollback data read in the
                // scanBlockScalarBreaksToSlice() call.
                buf = [];
                // The line breaks should actually be written _after_ the if() block
                // below. We work around that by inserting
                scanBlockScalarBreaksToSlice(indent, buf, endMark);

                // This will not run during the last iteration (see the if() vs the
                // while()), hence breaksTransaction rollback (which happens after this
                // loop) will never roll back data written in this if() block.
                if(reader_.column == indent && !reader_.empty)
                {
                    // Unfortunately, folding rules are ambiguous.

                    // This is the folding according to the specification:
                    if(style == ScalarStyle.folded && lineBreak == '\n' &&
                       leadingNonSpace && !reader_.front.among!(' ', '\t'))
                    {
                        // No breaks were scanned; no need to insert the space in the
                        // middle of slice.
                        if(buf.length == 0)
                        {
                            buf ~= ' ';
                        }
                    }
                    else
                    {
                        // We need to insert in the middle of the slice in case any line
                        // breaks were scanned.
                        //TODO: make this less terrible
                        string x;
                        x ~= lineBreak;
                        buf = x ~ buf;
                    }

                    ////this is Clark Evans's interpretation (also in the spec
                    ////examples):
                    //
                    //if(style == ScalarStyle.folded && lineBreak == '\n')
                    //{
                    //    if(startLen == endLen)
                    //    {
                    //        if(!" \t"d.canFind(reader_.front))
                    //        {
                    //            reader_.sliceBuilder.write(' ');
                    //        }
                    //        else
                    //        {
                    //            chunks ~= lineBreak;
                    //        }
                    //    }
                    //}
                    //else
                    //{
                    //    reader_.sliceBuilder.insertBack(lineBreak, endLen - startLen);
                    //}
                }
                else
                {
                    break;
                }
            }

            // If chompint is Keep, we keep (commit) the last scanned line breaks
            // (which are at the end of the scalar). Otherwise re remove them (end the
            // transaction).
            if(chomping == Chomping.keep)
            {
                // If chomping is Keep, we keep the line break but the first line break
                // that isn't stripped (since chomping isn't Strip in this branch) must
                // be inserted _before_ the other line breaks.
                if (lineBreak != int.max)
                {
                    slice ~= lineBreak;
                }
                slice ~= buf;
            }
            if(!chomping.among(Chomping.strip, Chomping.keep) && lineBreak != int.max)
            {
                // If chomping is not Keep, breaksTransaction was cancelled so we can
                // directly write the first line break (as it isn't stripped - chomping
                // is not Strip)
                slice ~= lineBreak;
            }

            return scalarToken(startMark, endMark, slice, style);
        }

        /// Scan chomping and indentation indicators of a scalar token.
        Tuple!(Chomping, int) scanBlockScalarIndicators(const Mark startMark) @safe
        {
            auto chomping = Chomping.clip;
            int increment = int.min;
            dchar c       = reader_.front;

            /// Indicators can be in any order.
            if(getChomping(c, chomping))
            {
                getIncrement(c, increment, startMark);
            }
            else
            {
                const gotIncrement = getIncrement(c, increment, startMark);
                if(gotIncrement) { getChomping(c, chomping); }
            }

            enforce(c.isBreakOrSpace,
                new ScannerException("While scanning a block scalar", startMark,
                expected("chomping or indentation indicator", c), reader_.mark));

            return tuple(chomping, increment);
        }

        /// Get chomping indicator, if detected. Return false otherwise.
        ///
        /// Used in scanBlockScalarIndicators.
        ///
        /// Params:
        ///
        /// c        = The character that may be a chomping indicator.
        /// chomping = Write the chomping value here, if detected.
        bool getChomping(ref dchar c, ref Chomping chomping) @safe
        {
            if(!c.among!('+', '-')) { return false; }
            chomping = c == '+' ? Chomping.keep : Chomping.strip;
            reader_.popFront();
            c = reader_.front;
            return true;
        }

        /// Get increment indicator, if detected. Return false otherwise.
        ///
        /// Used in scanBlockScalarIndicators.
        ///
        /// Params:
        ///
        /// c         = The character that may be an increment indicator.
        ///             If an increment indicator is detected, this will be updated to
        ///             the next character in the Reader.
        /// increment = Write the increment value here, if detected.
        /// startMark = Mark for error messages.
        bool getIncrement(ref dchar c, ref int increment, const Mark startMark) @safe
        {
            if(!c.isDigit) { return false; }
            // Convert a digit to integer.
            increment = c - '0';
            assert(increment < 10 && increment >= 0, "Digit has invalid value");

            enforce(increment > 0,
                new ScannerException("While scanning a block scalar", startMark,
                    expected("indentation indicator in range 1-9", "0"), reader_.mark));

            reader_.popFront();
            c = reader_.front;
            return true;
        }

        /// Scan (and ignore) ignored line in a block scalar.
        void skipBlockScalarIgnoredLine(const Mark startMark) @safe
        {
            findNextNonSpace();
            if(reader_.front== '#') { scanToNextBreak(); }

            enforce(reader_.front.isBreak,
                new ScannerException("While scanning a block scalar", startMark,
                    expected("comment or line break", reader_.front), reader_.mark));

            scanLineBreak();
        }

        /// Scan indentation in a block scalar, returning line breaks, max indent and end mark.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanBlockScalarIndentationToSlice(out uint maxIndent, out Mark endMark) @safe
        {
            string buf;
            endMark = reader_.mark;

            while(!reader_.empty && reader_.front.isBreakOrSpace)
            {
                if(reader_.front != ' ')
                {
                    buf ~= scanLineBreak();
                    endMark = reader_.mark;
                    continue;
                }
                reader_.popFront();
                maxIndent = max(reader_.column, maxIndent);
            }

            return buf;
        }

        /// Scan line breaks at lower or specified indentation in a block scalar.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        void scanBlockScalarBreaksToSlice(const uint indent, ref string buf, out Mark endMark) @safe
        {
            endMark = reader_.mark;

            for(;;)
            {
                while(!reader_.empty && reader_.column < indent && reader_.front == ' ') { reader_.popFront(); }
                if(reader_.empty || !reader_.front.isBreak)  { break; }
                buf ~= scanLineBreak();
                endMark = reader_.mark;
            }
        }

        /// Scan a qouted flow scalar token with specified quotes.
        Token scanFlowScalar(const ScalarStyle quotes) @safe
        {
            const startMark = reader_.mark;
            const quote     = reader_.front;
            reader_.popFront();

            string slice;
            // Reserve a reasonable number of characters.
            slice.reserve(expectedLineLength);

            scanFlowScalarNonSpacesToSlice(quotes, startMark, slice);

            while(reader_.front != quote)
            {
                scanFlowScalarSpacesToSlice(startMark, slice);
                scanFlowScalarNonSpacesToSlice(quotes, startMark, slice);
            }
            reader_.popFront();

            return scalarToken(startMark, reader_.mark, slice, quotes);
        }

        /// Scan nonspace characters in a flow scalar.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        void scanFlowScalarNonSpacesToSlice(const ScalarStyle quotes, const Mark startMark, ref string buf)
            @safe
        {
            for(;;)
            {
                while(!reader_.empty && !reader_.front.isFlowScalarBreakSpace)
                {
                    buf ~= reader_.front;
                    reader_.popFront();
                }
                enforce(!reader_.empty,
                    new ScannerException("While reading a flow scalar", startMark,
                        "reached end of file", reader_.mark));

                dchar c = reader_.front;
                if(quotes == ScalarStyle.singleQuoted && c == '\'' && (reader_.length >= 2) && (reader_[1] == '\''))
                {
                    reader_.popFront();
                    reader_.popFront();
                    buf ~= '\'';
                }
                else if((quotes == ScalarStyle.doubleQuoted && c == '\'') ||
                        (quotes == ScalarStyle.singleQuoted && c.among!('"', '\\')))
                {
                    reader_.popFront();
                    buf ~= c;
                }
                else if(quotes == ScalarStyle.doubleQuoted && c == '\\')
                {
                    reader_.popFront();
                    c = reader_.front;
                    if(c.among!(escapes))
                    {
                        reader_.popFront();
                        buf ~= '\\';
                        buf ~= c;
                    }
                    else if(c.among!(escapeHexCodeList))
                    {
                        const hexLength = dyaml.escapes.escapeHexLength(c);
                        reader_.popFront();
                        enforce(reader_.length >= hexLength,
                            new ScannerException("While scanning a double quoted scalar", startMark,
                                  "unexpected end of input within escape sequence", reader_.mark));

                        auto hex = reader_[0 .. hexLength];
                        enforce(hex.byCodeUnit.all!isHexDigit,
                            new ScannerException("While scanning a double quoted scalar", startMark,
                                expected("escape sequence of hexadecimal numbers",
                                    hex), reader_.mark));
                        reader_.popFrontN(hexLength);

                        buf ~= '\\';
                        buf ~= c;
                        buf ~= hex;

                    }
                    else if(c.isBreak)
                    {
                        scanLineBreak();
                        bool unused;
                        scanFlowScalarBreaksToSlice(startMark, buf, unused);
                    }
                    else
                    {
                        throw new ScannerException("While scanning a double quoted scalar", startMark,
                              text("found unsupported escape character ", c),
                              reader_.mark);
                    }
                }
                else { break; }
            }
        }

        /// Scan space characters in a flow scalar.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// spaces into that slice.
        void scanFlowScalarSpacesToSlice(const Mark startMark, ref string buf) @safe
        {
            const whitespaces = reader_.getSliceUntil!(x => !x.among!(' ', '\t'));

            enforce(!reader_.empty,
                new ScannerException("While scanning a quoted scalar", startMark,
                    "found unexpected end of buffer", reader_.mark));

            // Spaces not followed by a line break.
            if(!reader_.front.isBreak)
            {
                buf ~= whitespaces;
                return;
            }

            // There's a line break after the spaces.
            const lineBreak = scanLineBreak();

            if(lineBreak != '\n') { buf ~= lineBreak; }

            // If we have extra line breaks after the first, scan them into the
            // slice.
            bool extraBreaks;
            scanFlowScalarBreaksToSlice(startMark, buf, extraBreaks);

            // No extra breaks, one normal line break. Replace it with a space.
            if(lineBreak == '\n' && !extraBreaks) { buf ~= ' '; }
        }

        /// Scan line breaks in a flow scalar.
        void scanFlowScalarBreaksToSlice(const Mark startMark, ref string buf, out bool anyBreaks) @safe
        {
            bool end() @safe pure
            {
                if ((reader_.length < 3) || !reader_.startsWith("...", "---"))
                {
                    return false;
                }
                return reader_.length == 3 || reader_[3].isWhiteSpace;
            }
            for(;;)
            {
                // Instead of checking indentation, we check for document separators.
                enforce(!end,
                    new ScannerException("While scanning a quoted scalar", startMark,
                        "found unexpected document separator", reader_.mark));

                // Skip any whitespaces.
                reader_.popUntil!(x => !x.among!(' ', '\t'));

                // Encountered a non-whitespace non-linebreak character, so we're done.
                if(reader_.empty || !reader_.front.isBreakOrSpace)
                {
                    break;
                }

                anyBreaks = true;
                buf ~= scanLineBreak();
            }
        }

        /// Scan plain scalar token (no block, no quotes).
        Token scanPlain() @safe
        {
            // We keep track of the allowSimpleKey_ flag here.
            // Indentation rules are loosed for the flow context
            const startMark = reader_.mark;
            Mark endMark = startMark;
            const indent = indent_ + 1;

            string slice;
            // We allow zero indentation for scalars, but then we need to check for
            // document separators at the beginning of the line.
            // if(indent == 0) { indent = 1; }

            string buf;
            // Reserve a reasonable number of characters.
            buf.reserve(expectedLineLength);
            // Stop at a comment.
            while(!reader_.empty && reader_.front != '#')
            {
                bool appended;
                // Scan the entire plain scalar.
                for(;;)
                {
                    auto copy = reader_.save();
                    if (!copy.empty)
                    {
                        copy.popFront();
                    }
                    if(reader_.empty || reader_.front.isWhiteSpace ||
                       (flowLevel_ == 0 && reader_.front == ':' && copy.front.isWhiteSpace) ||
                       (flowLevel_ > 0 && reader_.front.among!(',', ':', '?', '[', ']', '{', '}')))
                    {
                        break;
                    }
                    buf ~= reader_.front;
                    appended = true;
                    reader_.popFront();
                }

                // It's not clear what we should do with ':' in the flow context.
                enforce(flowLevel_ == 0 || reader_.front != ':' ||
                   reader_.length <= 2 ||
                   reader_.length >= 2 && (reader_[1].isWhiteSpace ||
                        reader_[1].isFlowIndicator),
                    new ScannerException("While scanning a plain scalar", startMark,
                        "found unexpected ':' . Please check " ~
                        "http://pyyaml.org/wiki/YAMLColonInFlowContext for details.",
                        reader_.mark));

                if(!appended) { break; }

                allowSimpleKey_ = false;

                endMark = reader_.mark;

                slice ~= buf;

                buf = scanPlainSpacesToSlice();
                buf.reserve(expectedLineLength);
                if(buf.length == 0 ||
                   (flowLevel_ == 0 && reader_.column < indent))
                {
                    break;
                }
            }

            return scalarToken(startMark, endMark, slice, ScalarStyle.plain);
        }

        /// Scan spaces in a plain scalar.
        ///
        string scanPlainSpacesToSlice() @safe
        {
            // The specification is really confusing about tabs in plain scalars.
            // We just forbid them completely. Do not use tabs in YAML!

            // Get as many plain spaces as there are.
            string whitespaces = reader_.getSliceUntil!(x => x != ' ').idup;

            if (reader_.empty)
            {
                return "";
            }

            if(!reader_.front.isNSChar)
            {
                // We have spaces, but no newline.
                if(whitespaces.length > 0) { return whitespaces; }
                return "";
            }

            // Newline after the spaces (if any)
            const lineBreak = scanLineBreak();
            allowSimpleKey_ = true;

            static bool end(Reader reader_) @safe pure
            {
                if (!reader_.startsWith("...", "---"))
                {
                    return false;
                }
                auto next = reader_[3 .. $];
                return next.empty || next.front.isWhiteSpace;
            }

            if(end(reader_)) { return ""; }

            bool extraBreaks;

            string buf;
            if(lineBreak != '\n') { buf ~= lineBreak; }
            while(reader_.startsWith(nsChar))
            {
                if(reader_.startsWith(' ')) { reader_.popFront(); }
                else
                {
                    buf ~= scanLineBreak();
                    extraBreaks  = true;

                    if(end(reader_)) { return ""; }
                }
            }

            // No line breaks, only a space.
            if(lineBreak == '\n' && !extraBreaks) { buf ~= ' '; }
            return buf;
        }

        /// Scan handle of a tag token.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanTagHandleToSlice(string name)(const Mark startMark)
        {
            enum contextMsg = "While scanning a " ~ name;
            enforce(reader_.front == '!',
                new ScannerException(contextMsg, startMark, expected("'!'", reader_.front), reader_.mark));

            string buf = "!";
            reader_.popFront();

            if(reader_.front != ' ')
            {
                buf ~= reader_.getSliceUntil!(x => !x.isAlphaNum && !x.among!('-', '_'));
                enforce(reader_.front == '!',
                    new ScannerException(contextMsg, startMark, expected("'!'", reader_.front), reader_.mark));
                buf ~= "!";
                reader_.popFront();
            }

            return buf;
        }

        /// Scan URI in a tag token.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanTagURIToSlice(string name)(const Mark startMark)
        {
            // Note: we do not check if URI is well-formed.
            string buf;
            // Reserve a reasonable number of characters.
            buf.reserve(expectedLineLength);

            while(reader_.front.isAlphaNum || reader_.front.isURIChar)
            {
                if(reader_.front == '%')
                {
                    buf ~= scanURIEscapesToSlice!name(startMark);
                }
                else
                {
                    buf ~= reader_.front;
                    reader_.popFront();
                }
            }
            // OK if we scanned something, error otherwise.
            enum contextMsg = "While parsing a " ~ name;
            enforce(buf.length > 0,
                new ScannerException(contextMsg, startMark, expected("URI", reader_.front), reader_.mark));
            return buf;
        }

        // Not @nogc yet because std.utf.decode is not @nogc
        /// Scan URI escape sequences.
        ///
        /// Assumes that the caller is building a slice in Reader, and puts the scanned
        /// characters into that slice.
        string scanURIEscapesToSlice(string name)(const Mark startMark)
        {
            // URI escapes encode a UTF-8 string. We store UTF-8 code units here for
            // decoding into UTF-32.
            string buffer;


            enum contextMsg = "While scanning a " ~ name;
            while(reader_.front == '%')
            {
                reader_.popFront();
                char[2] nextByte = reader_[0 .. 2];
                reader_.popFront();
                reader_.popFront();

                enforce(nextByte[0].isHexDigit && nextByte[1].isHexDigit,
                    new ScannerException(contextMsg, startMark,
                        expected("URI escape sequence of 2 hexadecimal " ~
                            "numbers", nextByte), reader_.mark));
                buffer ~= nextByte[].to!ubyte(16);

            }
            try
            {
                buffer.validate();
                return buffer;
            }
            catch (UTFException)
            {
                throw new ScannerException(contextMsg, startMark,
                        "Invalid UTF-8 data encoded in URI escape sequence",
                        reader_.mark);
            }
        }


        /// Scan a line break, if any.
        ///
        /// Transforms:
        ///   '\r\n'      :   '\n'
        ///   '\r'        :   '\n'
        ///   '\n'        :   '\n'
        ///   '\u0085'    :   '\n'
        ///   '\u2028'    :   '\u2028'
        ///   '\u2029     :   '\u2029'
        ///   no break    :   '\0'
        dchar scanLineBreak() @safe
        {
            const c = reader_.front;
            if (c == '\r')
            {
                reader_.popFront();
                if (reader_.front == '\n')
                {
                    reader_.popFront();
                }
                return '\n';
            }
            if (c == '\n')
            {
                reader_.popFront();
                return '\n';
            }
            if(c == '\x85')
            {
                reader_.popFront();
                return '\n';
            }
            if(c == '\u2028' || c == '\u2029')
            {
                reader_.popFront();
                return c;
            }
            return '\0';
        }
}
