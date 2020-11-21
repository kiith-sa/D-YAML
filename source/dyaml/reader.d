
//          Copyright Ferdinand Majerech 2011-2014.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

module dyaml.reader;


import core.stdc.stdlib;
import core.stdc.string;
import core.thread;

import std.algorithm;
import std.array;
import std.conv;
import std.exception;
import std.range;
import std.string;
import std.system;
import std.typecons;
import std.utf;

import tinyendian;

import dyaml.encoding;
import dyaml.exception;

alias isBreak = among!('\n', '\u0085', '\u2028', '\u2029');

package:


///Exception thrown at Reader errors.
class ReaderException : YAMLException
{
    this(string msg, string file = __FILE__, size_t line = __LINE__)
        @safe pure nothrow
    {
        super("Reader error: " ~ msg, file, line);
    }
}

/// Provides an API to read characters from a UTF-8 buffer while keeping track
/// of the position.
struct Reader
{
    private:
        // Buffer of currently loaded characters.
        const(char)[] buffer_;

        // Index of the current character in the buffer.
        size_t charIndex_;

        // Current line in file.
        uint line_;
        // Current column in file.
        uint column_;

    public:
        /// Construct a Reader.
        ///
        /// Params:  buffer = Buffer with YAML data. This may be e.g. the entire
        ///                   contents of a file or a string. $(B will) be modified by
        ///                   the Reader and other parts of D:YAML (D:YAML tries to
        ///                   reuse the buffer to minimize memory allocations)
        ///
        /// Throws:  ReaderException on a UTF decoding error or if there are
        ///          nonprintable Unicode characters illegal in YAML.
        this(ubyte[] buffer) @safe pure
        {
            auto endianResult = fixUTFByteOrder(buffer);
            if(endianResult.bytesStripped > 0)
            {
                throw new ReaderException("Size of UTF-16 or UTF-32 input not aligned " ~
                                          "to 2 or 4 bytes, respectively");
            }

            auto utf8Result = toUTF8(endianResult.array, endianResult.encoding);
            const msg = utf8Result.errorMessage;
            if(msg !is null)
            {
                throw new ReaderException("Error when converting to UTF-8: " ~ msg);
            }

            this(utf8Result.utf8);
        }
        this(const(char)[] buffer) @safe pure
        {
            buffer_ = buffer;
            enforce(isPrintableValidUTF8(buffer_),
                    new ReaderException("Special unicode characters are not allowed"));
        }


        auto save() @safe pure
        {
            return this;
        }

        bool empty() @safe pure nothrow const @nogc
        {
            return buffer_.length == 0;
        }

        /// Get the next character in the buffer.
        dchar front() @safe pure const
        {
            assert(!empty, "Trying to read past the end of the buffer");

            return buffer_.front;
        }

        /// Move current position forward by one character.
        void popFront() @safe pure
        {
            ++charIndex_;

            // UTF-8
            assert(!buffer_.empty,
                   "Attempted to decode past the end of YAML buffer");

            const c = buffer_.front;

            buffer_.popFront();

            if(c.isBreak || (c == '\r' && buffer_.front != '\n'))
            {
                ++line_;
                column_ = 0;
            }
            else if(c != '\uFEFF') { ++column_; }
        }

        auto opSlice(size_t a, size_t b) @safe pure
        {
            return buffer_[a..b];
        }
        alias opDollar = length;
        auto opIndex(size_t idx) @safe pure
        {
            return buffer_[idx];
        }
        auto length() @safe pure
        {
            return buffer_.length;
        }

        /// Get a string describing current buffer position, used for error messages.
        Mark mark() const pure nothrow @nogc @safe { return Mark(line_, column_); }

        /// Get current line number.
        uint line() const @safe pure nothrow @nogc { return line_; }

        /// Get current column number.
        uint column() const @safe pure nothrow @nogc { return column_; }

        /// Get index of the current character in the buffer.
        size_t charIndex() const @safe pure nothrow @nogc { return charIndex_; }
}

package auto popUntil(alias pred, R)(ref R reader)
{
    while(!reader.empty && !pred(reader.front))
    {
        reader.popFront();
    }
}

package auto getSliceUntil(alias pred, R)(ref R reader)
{
    const chars = reader.countUntil!pred;
    const sliceLen = chars >= 0 ? chars : reader.length;
    assert(sliceLen <= reader.length);
    auto slice = reader[0 .. sliceLen];
    reader.popFrontN(sliceLen);
    return slice;
}

//Todo: proper constraints

template matches(rules...) {
    bool matches(T)(T range) {
        static foreach (e; rules) {
            if (range.empty) {
                return false;
            }
            static if (__traits(compiles, (range.front == e))) {
                if (range.front == e) {
                    range.popFront();
                } else {
                    return false;
                }
            } else {
                if (e(range.front)) {
                    range.popFront();
                } else {
                    return false;
                }
            }
        }
        return true;
    }
}

private:

// Convert a UTF-8/16/32 buffer to UTF-8, in-place if possible.
//
// Params:
//
// input    = Buffer with UTF-8/16/32 data to decode. May be overwritten by the
//            conversion, in which case the result will be a slice of this buffer.
// encoding = Encoding of input.
//
// Returns:
//
// A struct with the following members:
//
// $(D string errorMessage)   In case of an error, the error message is stored here. If
//                            there was no error, errorMessage is NULL. Always check
//                            this first.
// $(D char[] utf8)           input converted to UTF-8. May be a slice of input.
// $(D size_t characterCount) Number of characters (code points) in input.
auto toUTF8(ubyte[] input, const UTFEncoding encoding) @safe pure nothrow
{
    // Documented in function ddoc.
    struct Result
    {
        string errorMessage;
        char[] utf8;
        size_t characterCount;
    }

    Result result;

    // Encode input_ into UTF-8 if it's encoded as UTF-16 or UTF-32.
    //
    // Params:
    //
    // buffer = The input buffer to encode.
    // result = A Result struct to put encoded result and any error messages to.
    //
    // On error, result.errorMessage will be set.
    static void encode(C)(C[] input, ref Result result) @safe pure
    {
        // We can do UTF-32->UTF-8 in place because all UTF-8 sequences are 4 or
        // less bytes.
        static if(is(C == dchar))
        {
            char[4] encodeBuf;
            auto utf8 = cast(char[])input;
            auto length = 0;
            foreach(dchar c; input)
            {
                ++result.characterCount;
                // ASCII
                if(c < 0x80)
                {
                    utf8[length++] = cast(char)c;
                    continue;
                }

                std.utf.encode(encodeBuf, c);
                const bytes = codeLength!char(c);
                utf8[length .. length + bytes] = encodeBuf[0 .. bytes];
                length += bytes;
            }
            result.utf8 = utf8[0 .. length];
        }
        // Unfortunately we can't do UTF-16 in place so we just use std.conv.to
        else
        {
            result.characterCount = std.utf.count(input);
            result.utf8 = input.to!(char[]);
        }
    }

    try final switch(encoding)
    {
        case UTFEncoding.UTF_8:
            result.utf8 = cast(char[])input;
            result.utf8.validate();
            result.characterCount = std.utf.count(result.utf8);
            break;
        case UTFEncoding.UTF_16:
            assert(input.length % 2 == 0, "UTF-16 buffer size must be even");
            encode(cast(wchar[])input, result);
            break;
        case UTFEncoding.UTF_32:
            assert(input.length % 4 == 0, "UTF-32 buffer size must be a multiple of 4");
            encode(cast(dchar[])input, result);
            break;
    }
    catch(ConvException e) { result.errorMessage = e.msg; }
    catch(UTFException e)  { result.errorMessage = e.msg; }
    catch(Exception e)
    {
        assert(false, "Unexpected exception in encode(): " ~ e.msg);
    }

    return result;
}

/// Determine if all characters (code points, not bytes) in a string are printable.
bool isPrintableValidUTF8(T)(const T[] chars) @safe pure
{
    import std.uni : isControl, isWhite;
    foreach (dchar chr; chars)
    {
        if (!chr.isValidDchar || (chr.isControl && !chr.isWhite))
        {
            return false;
        }
    }
    return true;
}

/// Counts the number of ASCII characters in buffer until the first UTF-8 sequence.
///
/// Used to determine how many characters we can process without decoding.
size_t countASCII(const(char)[] buffer) @safe pure nothrow @nogc
{
    return buffer.byCodeUnit.until!(x => x > 0x7F).walkLength;
}
// Unittests.

void testPeekPrefixForward(R)()
{
    import std.encoding : BOM, bomTable;
    ubyte[] data = bomTable[BOM.utf8].sequence ~ "data".representation.dup;
    auto reader = new R(data);
    assert(reader.front == 'd');
    reader.popFront();
    assert(reader.front == 'a');
    reader.popFront();
    assert(reader.front == 't');
    reader.popFront();
    assert(!reader.empty);
    assert(reader.front == 'a');
    reader.popFront();
    assert(reader.empty);
}

void testUTF(R)()
{
    import std.encoding;
    auto data = "data";
    void utf_test(T)(T[] data, BOM bom)
    {
        ubyte[] bytes = bomTable[bom].sequence ~
                        (cast(ubyte[])data)[0 .. data.length * T.sizeof];
        auto reader = new R(bytes);
        assert(reader.front == 'd');
        reader.popFront();
        assert(reader.front == 'a');
        reader.popFront();
        assert(reader.front == 't');
        reader.popFront();
        assert(reader.front == 'a');
        reader.popFront();
        assert(reader.empty);
    }
    utf_test!char(to!(char[])(data), BOM.utf8);
    utf_test!wchar(to!(wchar[])(data), endian == Endian.bigEndian ? BOM.utf16be : BOM.utf16le);
    utf_test!dchar(to!(dchar[])(data), endian == Endian.bigEndian ? BOM.utf32be : BOM.utf32le);
}

void test1Byte(R)()
{
    ubyte[] data = [97];

    auto reader = new R(data);
    assert(reader.front == 'a');
    assert(!reader.empty);
    reader.popFront();
    assert(reader.empty);
}

@safe unittest
{
    testPeekPrefixForward!Reader();
    testUTF!Reader();
    test1Byte!Reader();
}
//Issue 257 - https://github.com/dlang-community/D-YAML/issues/257
@safe unittest
{
    import dyaml.loader : Loader;
    auto yaml = "hello ";
    auto root = Loader.fromString(yaml).load();

    assert(root.isValid);
}

@safe unittest
{
    {
        auto data = "       ";
        auto reader = Reader(data);
        assert(reader.getSliceUntil!(x => x != ' ') == data);
        assert(reader.empty);
    }
    {
        auto data = "    z   ";
        auto reader = Reader(data);
        assert(reader.getSliceUntil!(x => x != ' ') == "    ");
        assert(reader.front == 'z');
    }
}
