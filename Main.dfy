include "SourceScanner.dfy"
include "SourceParser.dfy"
include "SourcePrinter.dfy"

extern "InputRead"
method InputRead() returns (input: array<char>)
  ensures input != null
  decreases *

method Main()
  decreases *
{
  var chars := InputRead();
  var stringTokens := SourceScannerRead(chars);
  var parser := new Parser(stringTokens);
  var success, prog := parser.Parse();
  if success {
    print "Parse succeeded!\n";
    var pr := new SourcePrinter;
    pr.PrintProgram(prog);
  } else {
    print "Parse failed :(\n";
  }
}
