
//          Copyright Ferdinand Majerech 2011.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

module dyaml.test.reader;

@safe unittest
{
    import std.exception :assertThrown;

    import dyaml.test.common : readData, run;
    import dyaml.reader : Reader, ReaderException;

    /**
    Try reading entire file through Reader, expecting an error (the file is invalid).

    Params:  data    = Stream to read.
    */
    static void runReader(ubyte[] fileData) @safe
    {
        auto reader = new Reader(fileData);
        while(!reader.empty) { reader.popFront(); }
    }

    /**
    Stream error unittest. Tries to read invalid input files, expecting errors.

    Params:  errorFilename = File name to read from.
    */
    static void testStreamError(string errorFilename) @safe
    {
        assertThrown!ReaderException(runReader(readData(errorFilename)));
    }
    run(&testStreamError, ["stream-error"]);
}
