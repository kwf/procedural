include "SourceScanner.dfy"
include "SourceParser.dfy"

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
    print prog, "\n";  // this may not be pretty
  } else {
    print "Parse failed :(\n";
  }
}
