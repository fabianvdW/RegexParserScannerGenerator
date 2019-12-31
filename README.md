# RegexParserScannerGenerator

A tool for parsing regular expressions, and checking whether given words are in the language of the regular expression. This can be done by either running an interpreter (slow for long words) or generating an acceptor, and using this. A generated acceptor can be used multiple times for checking different words.

The generated acceptor, or bytecode interpreter is a DFA. The only step thus missing for this tool to be a complete scanner generator is to generate the code which simulates a DFA.

# Usage
```
> git clone https://github.com/fabianvdW/RegexParserScannerGenerator.git
> cd RegexParserScannerGenerator
```
```FSharp
dotnet fsi ScannerGenerator.fs
open ScannerGenerator;;
> let (regex,alphabet) = ("(a|b)?ccc(a|b)+", ["a";"b";"c"]);;

//Convert to internal Regex struct. Parsing is done here
> let regex = match Regex.parse(regex,alphabet) with |Ok(regex)->regex;;

//Check if parsing was correct
> regex.to_string();;
val it : System.String =
  "<Regex with
Alphabet : ["a"; "b"; "c"]
Expression : (a|b)?·c·c·c·(a|b)+
>"

//Interpret expression
> tokenize ("acccabab", regex.alphabet) |> regex.expression.interpret_expression;;
val it : bool = true
> tokenize ("cca", regex.alphabet) |> regex.expression.interpret_expression;;
val it : bool = false

//Generate acceptor
> let acceptor = regex.generate_acceptor();;
val acceptor : (System.String -> bool)
> acceptor "acccabab";;
val it : bool = true
> acceptor "cca";;
val it : bool = false

//View NFA + DFA of Regex
> let nfa = fst (regex.expression.convert_to_nfa(regex.alphabet,true));;
val nfa : NFA =
  Regular
    (false,
     [|[Regular
          (false,
          .
          .
          . //Is pretty big
> let dfa = nfa.convert_to_dfa(regex.alphabet);;
val dfa : DFA =
  Regular
    (false,
     [|Regular
         (false,
         .
         .
         . //Is also pretty big
         
//We can also use the dfa to interpret expressions.
//Converting Regex -> NFA and NFA -> DFA, and simulating expressions there, is exactly the same as generate_acceptor()
> (tokenize ("acccabab", regex.alphabet),regex.alphabet) |> dfa.interpreter_expression;;
val it : bool = true

//Showcase of extremums
> let (alphabet, regex) = (["a";"b"], "((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*");;
> let regex = match Regex.parse(regex,alphabet) with |Ok(regex)->regex;;
> let acceptor = regex.generate_acceptor();; //This already takes a few seconds. But looking at the expression, this is okay.
> acceptor "aabaabaabaabaabaabaabaabaabaab";;
val it : bool = true
> acceptor "aabaabaabaabaabaabaabaabaabaa";;
val it : bool = false
```
