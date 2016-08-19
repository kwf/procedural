include "Prelude.dfy"

method SourceScannerRead(input: array<char>) returns (stringTokens: array<string>)
  requires input != null
  ensures stringTokens != null
{
  var xs, i, N := Nil, 0, input.Length;
  while true
    invariant 0 <= i <= N
    decreases N - i
  {
    // skip white space
    while i < N && IsWhiteSpace(input[i])
      invariant i <= N
    { i := i + 1; }
    if i == N { break; }
    // scan next token and add it to xs
    var start, next := i, input[i];
    i := i + 1;
    if IsDigit(next) {
      // number
      while i < N && IsDigit(input[i])
        invariant i <= N
      { i := i + 1; }
    } else if IsLetterLike(next) {
      // identifier
      while i < N && (IsLetterLike(input[i]) || IsDigit(input[i]))
        invariant i <= N
      { i := i + 1; }
    } else if next == '"' {
      // string literal
      while i < N && input[i] != '"'
        invariant i <= N
      { i := i + 1; }
    } else if IsSinglePunctuation(next) {
      // single-character punctuation token
    } else {
      while i < N
        invariant i <= N
      {
        var ch := input[i];
        if IsWhiteSpace(ch) || IsLetterLike(ch) || IsDigit(ch) || ch == '"' || IsSinglePunctuation(ch) {
          break;
        }
        i := i + 1;
      }
    }
    xs := Cons(input[start..i], xs);
  }
  stringTokens := ListToArray(xs);
}

predicate method IsWhiteSpace(ch: char) {
  ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n'
}
predicate method IsDigit(ch: char) {
  '0' <= ch <= '9'
}
predicate method IsLetterLike(ch: char) {
  ('a' <= ch <= 'z') ||
  ('A' <= ch <= 'Z') ||
  ch == '_'
}
predicate method IsSinglePunctuation(ch: char) {
  ch == '(' || ch == ')'
}

method ListToArray<T>(xs: List<T>) returns (a: array<T>)
  ensures a != null
{
  a := new T[Length(xs)];
  var i, ys := Length(xs), xs;
  while i != 0
    invariant 0 <= i == Length(ys) <= Length(xs)
  {
    i := i - 1;
    a[i], ys := ys.Head, ys.Tail;
  }
}
