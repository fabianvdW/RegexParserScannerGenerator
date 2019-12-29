//author : Fabian von der Warth
//Angelehnt an : Grundlagen der Programmierung, Ralf Hinze TU KL WS 19/20, https://pl.cs.uni-kl.de/homepage/de/teaching/ws19/gdp/
module ScannerGenerator
open System

type Expression<'T when 'T: equality> =
    |Epsilon // €
    |Empty // o/
    |Literal of 'T
    |Cons of Expression<'T>*Expression<'T> //a·b
    |Alternative of Expression<'T>*Expression<'T> // (a|b)
    |Star of Expression<'T> //Kleeneshe Hülle (*)
    |Plus of Expression<'T> // positive Kleenesche Hülle (+)
    |QMark of Expression<'T> // ? Optional
    // Präzedenz: Literal=Empty=Epsilon > ? = + = * > · > |
    member this.interpret_expression<'T when 'T: equality>(input: 'T list): bool =
        match input with
            | [] -> this.nullable()
            | head::tail -> this.divide(head).interpret_expression(tail)

    member this.divide<'T when 'T : equality>(l: 'T) : Expression<'T> = 
        match this with
            |Epsilon|Empty -> Empty
            |Literal other -> if other = l then Epsilon else Empty
            |Cons (e1, e2) -> if e1.nullable() then Alternative(Cons(e1.divide(l),e2),e2.divide(l)) else Cons(e1.divide(l), e2)
            |Alternative (e1, e2) -> Alternative(e1.divide(l), e2.divide(l))
            |Star e1 -> Cons(e1.divide(l), Star e1)
            |Plus e1 -> Cons(e1.divide(l), Star e1)
            |QMark e1 -> e1.divide(l)

    member this.nullable(): bool = 
        match this with
            | Epsilon -> true
            | Empty -> false
            | Literal _ -> false
            | Cons (e1, e2) -> e1.nullable() && e2.nullable()
            | Alternative (e1, e2) -> e1.nullable() || e2.nullable()
            | Star _ -> true
            | Plus e -> e.nullable()
            | QMark _ -> true
    //Helper method for parsing - detmerines if an expression is fully parsed already
    member this.contains_null () : bool =
        match this with
            | Epsilon -> true
            | Empty -> true
            | Literal _ -> false
            | Cons (a, b) -> a.contains_null() || b.contains_null()
            | Alternative (a, b) -> a.contains_null() || b.contains_null()
            | Star a | Plus a | QMark a -> a.contains_null()

    member this.to_string (priority:int) : String =
        match this with
            | Epsilon -> "ε"
            | Empty -> "∅"
            | Literal s -> s.ToString()
            | Cons (s1, s2) -> (if priority > 1 then "(" else "") + ((1) |> s1.to_string) + "·" + ((1) |> s2.to_string) + if priority > 1 then ")" else ""
            | Alternative (s1, s2) ->  (if priority > 0 then "(" else "") + ((0) |> s1.to_string) + "|"  + ((0) |> s2.to_string) + if priority >0 then ")" else ""
            | Star tail -> ((2) |> tail.to_string) + "*"
            | Plus tail -> ((2) |> tail.to_string) + "+"
            | QMark tail -> ((2) |> tail.to_string) + "?"

let rec alphabet_contains<'T when 'T :> IComparable<String>> (alphabet: 'T list, value: String) : Option<'T> =
    match alphabet with
        | [] -> None
        | head::tail -> if head.CompareTo(value) = 0 then Some(head) else alphabet_contains(tail, value)

//Tokenizer
//O(n)
let rec scan_forward<'T when 'T :> IComparable<String> and 'T:equality> (cursor:String, alphabet: 'T list) : Expression<'T> option * String =
    let rec tokenize(string_left: String, current_string:String) =
        if string_left.Length = 0 then
            (None, "")
        else
            if string_left.[0] = '(' || string_left.[0] = ')' then (None, string_left) else
            let (new_char, is_literal, rest) = match string_left.[0] with
                                                | '\\' -> (string_left.[0..1], true, string_left.[2..])
                                                | '?' | '+' | '*' | '·' | '|' ->  (string_left.[0..0], false, string_left.[1..])
                                                | _ -> (string_left.[0..0], true, string_left.[1..])
            if is_literal then
                match (alphabet, current_string+new_char) |> alphabet_contains with
                    | Some res -> (Some(Literal(res)), rest)
                    | None -> tokenize (rest, current_string+new_char)
            else                                            
                if current_string.Length = 0 then
                    (Some (match new_char with
                            | "?" -> QMark Empty
                            | "+" -> Plus Empty
                            | "*" -> Star Empty
                            | "·" -> Cons (Empty, Empty)
                            | "|" -> Alternative (Empty, Empty)
                            | _ -> failwith "///"), rest)
                else
                    (None, string_left)                    
    if cursor.StartsWith("(") || cursor.StartsWith(")") then
        scan_forward(cursor.[1..], alphabet)
    else
        tokenize (cursor, "")

//completes finished subtrees (only 1 at a time). Takes care of precedence via double iteration
//O(n)
let rec fold_expression_stack_once<'T when 'T : equality> (expr_s: Expression<'T> list, prio:int) : Expression<'T> list =
    match expr_s with 
        | smth::Cons (Empty, Empty)::smth2::rexpr_s when prio = 1 -> Cons(smth, smth2)::rexpr_s
        | smth::Alternative(Empty, Empty)::smth2::rexpr_s when prio = 0 -> Alternative(smth, smth2)::rexpr_s
        | smth::QMark Empty::rexpr_s -> QMark(smth)::rexpr_s
        | smth::Plus Empty::rexpr_s -> Plus(smth)::rexpr_s
        | smth::Star Empty::rexpr_s -> Star(smth)::rexpr_s
        | a::b::rexpr_s when (() |> a.contains_null |> not) && (() |> b.contains_null |> not) && prio = 1-> Cons(a,b)::rexpr_s
        | head::tail -> head::(fold_expression_stack_once (tail, prio))
        | [] -> []
//O(n*m) Worst Case O(n^2)
let rec fold_expression_stack<'T when 'T: equality> (expr_s: Expression<'T> list) : Expression<'T> list = 
    let fold = (expr_s, 2) |> fold_expression_stack_once
    if List.length fold < List.length expr_s then
        fold |> fold_expression_stack
    else
        let fold = (expr_s, 1) |> fold_expression_stack_once
        if List.length fold < List.length expr_s then
            fold |> fold_expression_stack
        else
            let fold = (fold, 0) |> fold_expression_stack_once
            if List.length fold < List.length expr_s then
                fold |> fold_expression_stack
            else
                expr_s

let remove_symbol(s:String, sym:Char):String = 
    String.collect (fun(x) -> if x <> sym then x.ToString() else "") s

type Regex<'T when 'T :> IComparable<String> and 'T:equality> = 
    { expression: Expression<'T>; alphabet : 'T list}

    member this.to_string (): String =
        (sprintf "<Regex with \nAlphabet : %A\nExpression : %s\n>" this.alphabet ((0) |> this.expression.to_string))
    //Infix Parsing - Etwas komplizierter
    //Von dem Alphabet wird an dieser Stelle die Eindeutigkeit erwartet ----> Ein Alphabet ["hallo"; "ha"] wäre invalide, da "hallo" mit "ha" anfängt
    //Dafür gibt es auch ein Fachbegriff, der ist mir aber entfallen.
    //Warum wird dies erwartet? Der String wird Character für Character nach validen Literalen des Alphabets durchgegangen, diese werden falls benötigt zusammengebaut
    //Falls Keywords "*,+,?,(,),·" in Literalen verwendet werden, müssen diese im Regex und im Alphabet mit "\" escaped werden.
    //O(n^2) im Worst Case, wenn ich mich nicht täusche
    static member parse<'T when 'T :> IComparable<String>> (input:String, alphabet: 'T list) : Result<Regex<'T>, String> =
        let rec remove_trailing_brackets (s:String) : String =
            if s.StartsWith(")") then s.[1..]|>remove_trailing_brackets else s
        let rec inner (cursor:String, expr_s: Expression<'T> list): Result<(Regex<'T>*String), String> =
            if cursor.StartsWith("(") then
                let res = inner (cursor.[1..], [])
                match res with
                    | Ok v -> (if (fst v).expression.contains_null() then (snd v, expr_s) else (snd v, ((fst v).expression)::expr_s)) |> inner 
                    | _ -> res
            else
                let (token, rest) = scan_forward (cursor, alphabet)
                //printf "Cursor: %s ; Expr Stack: %A; Token: %A, Rest: %s\n\n" cursor expr_s token rest //DEBUG
                let expr_s = if token.IsSome then token.Value::expr_s else expr_s
                if token.IsNone || rest.StartsWith(")") then
                    if rest.Length = 0 || rest.StartsWith(")") then
                        let expr_s = expr_s |> List.rev |> fold_expression_stack
                        let rest = rest |> remove_trailing_brackets
                        //printfn "EXPR_S: %A" expr_s
                        if token.IsNone && ((((cursor, '(') |> remove_symbol), ')') |> remove_symbol).Length > 0 then Error "Invalid token" else
                        match expr_s with
                            | [single] -> Ok(({expression=single;alphabet=alphabet},rest))
                            | [] -> Ok(({expression=Epsilon;alphabet=alphabet},rest))
                            | _ -> Error ("Couldn't finish parsing")
                    else
                        Error ("String couldn't be tokenized. No valid token!")
                else
                    inner (rest, expr_s)
        let check_brackets(brackets: String) : bool =
            //printfn "%s" brackets //DEBUG
            let rec inner (s : String) : String =
                if s.Length = 0 then "" else
                if s.StartsWith("()") then inner s.[2..] else
                if s.StartsWith("(") then 
                    let temp = inner s.[1..]
                    if not (temp.StartsWith(")")) then "-" else inner(temp.[1..])
                else
                    s
            (inner brackets).Length = 0
        let rec remove_escape_brackets (remove: String) : String = 
             if remove.Length = 0 then remove else
             if remove.StartsWith("\(") || remove.StartsWith("\)") then remove.[2..] |> remove_escape_brackets else
             remove.[0..0] + (remove.[1..] |> remove_escape_brackets)
        if not ((String.collect (fun(x)-> if x = '(' || x= ')' then x.ToString() else "") (input|>remove_escape_brackets)) |> check_brackets) then Error "Invalid brackets!" else
        let res = inner (input,[])
        match res with
            | Ok (r,rest_str) -> if rest_str.Length = 0 then Ok(r) else Error "Invalid expression"
            | Error e -> Error(e)



//---------------------------------------------------------------------------------------------------
//Tests und IO
let infer_alphabet(input:String): String list = 
    let rec inner(rest:String, curr_alph: String list):String list= 
        if rest.Length = 0 then curr_alph else
        if List.contains rest.[0..0] curr_alph then inner(rest.[1..],curr_alph) else inner(rest.[1..], rest.[0..0]::curr_alph)
    inner(input, [])
let rec tokenize<'T when 'T:> IComparable<String> and 'T:equality>(input: String, alphabet: 'T list): 'T list =
    if input.Length = 0 then [] else 
    let (expr, rest) = scan_forward(input, alphabet)
    match expr with
        |Some (Literal l) -> l::(tokenize(rest, alphabet))
        | _ -> failwith "Illegal input string!"
let escape_symbols = ["(";")";"Ø";"*";"|";"+";"?";"·"]

let interpreter(regex:String, input:String) :bool= 
    //First infer alphabet
    let input = String.collect (fun(x) -> if List.contains (x.ToString()) escape_symbols then "\\"+x.ToString() else x.ToString()) input
    printfn "Interpreting Regex: %s with input: %s" regex input
    let alphabet = infer_alphabet input
    printfn "Infered alphabet: %A" alphabet
    let regex = Regex.parse (regex, alphabet)
    let regex = match regex with |Ok reg -> reg | Error msg -> failwith "Couldn't parse regex"
    printfn "Parsed Regex:\n %s" (regex.to_string())
    regex.expression.interpret_expression(tokenize (input, alphabet))

let parse_print<'T when 'T :> IComparable<String> and 'T: equality> (s : String, alphabet: 'T list) =
    match Regex.parse (s, alphabet) with
        | Ok reg -> sprintf "%s" (reg.expression.to_string(0))
        | Error msg -> sprintf "%s" msg
        
let regex_parse_tests() : unit =
    printfn "\n---------------------------------------------\n"
    let alphabet = ["a";"b";"c"]
    //General correctness
    let strings = ["a";"b";"a*";"b*";"ab";"ab*";"a*b";"(a?b?)+";"aaaaaa?(aaaaa)?aaaaa+(aaaa)+c*a+";"(a|b)*(a|b)*(a|b)";"b(a|b)*a";"(b(cb|aa*)c)*";"(a|b)*b(a|b)(b|a)";"((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*";"((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*"]
    for s in strings do
        let res = ((parse_print (s, alphabet)),'·') |> remove_symbol
        if s.Length < 120 then
            printfn "\"%s\" : %s" s res
        assert(s = res)
    //Simplification Abilities
    let strings = [("(a)(b)", "ab");("((((a))))()()(b)()", "ab");("(((())))(a(b))((()))(a)(b)","abab");("(a|b)","a|b");("(a|b*)","a|b*")]
    for s in strings do
        let res = ((parse_print (fst s, alphabet)),'·') |> remove_symbol
        printfn "\"%s\" : %s" (fst s) res
        assert(res = snd s)
    //Escape symbols
    let alphabet = ["\(";"\)";"\Ø";"\*";"\|";"\+";"\?";"\·"]
    let strings = ["\(";"\)";"\Ø";"\*";"\|";"\+";"\?";"\||\|";"\**";"\++"]
    for s in strings do
        let res = ((parse_print (s, alphabet)),'·') |> remove_symbol
        printfn "\"%s\" : %s" s res
        assert(s = res)
    printfn "\n---------------------------------------------\n"
    ()

let interpreter_tests() : unit =
    //Gerade noch rechtzeitig, um die Übungsaufgaben zu lösen :)
    printfn "%A" (interpreter ("b(a|b)*a", "bbaba"))
    printfn "%A" (interpreter ("(b(cb|aa*)c)*","bcbcbabc"))
    printfn "%A" (interpreter ("(a|b)*b(a|b)(b|a)","ababbbaba"))
    printfn "%A" (interpreter ("((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*","aabaabaabaabaabaabaabaabaabaab"))
[<EntryPoint>]
let main argv =
    //Regex to String testing
    let example:Regex<String>= {expression = Cons(Star(Alternative(Literal("a"),Literal("b"))), Cons(Literal("b"), QMark(Alternative(Literal("a"), Literal("b"))))); alphabet = ["a";"b"]}
    printfn "%s" (example.to_string ())

    //String to Regex testing
    printfn "\"(a|b)*b(a|b)?\"->Regex->String: %s" (parse_print("(a|b)*b(a|b)?", ["a";"b";]))
    regex_parse_tests()
    //Regex to acceptor testing
    interpreter_tests()
    0
