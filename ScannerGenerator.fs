//author : Fabian von der Warth
//Angelehnt an : Grundlagen der Programmierung, Ralf Hinze TU KL WS 19/20, https://pl.cs.uni-kl.de/homepage/de/teaching/ws19/gdp/
module ScannerGenerator
open System

//General functions
let same = LanguagePrimitives.PhysicalEquality
let same_x x = fun(y)->same x y
let unwrap option = match option with | Some(x)->x | _ -> failwith "Can't unwrap a None type"

//Set functions. Goes by reference equality
let rec contains set functor =
    List.exists (fun(x) -> functor (x)) set
let set_equals set1 set2 =
    if List.length set1 <> List.length set2 then false else
    not (List.exists (fun(x) -> not (contains set2 (same_x x))) set1)
let rec make_set non_set = 
    match non_set with
        | [] -> []
        | head::tail -> if contains tail (same_x head) then make_set tail else head::(make_set tail)
let rec set_union set1 set2 =
    match set1 with
        | [] -> set2
        | head::tail ->
            if contains set2 (same_x head) then set_union tail set2 else head::(set_union tail set2)
//Cache type for a bit of speed
type Cache<'T,'U> = (('T  * 'U) list)
let rec probe_cache_f (cache:Cache<'T,'U>) (functor:'T->bool)  :'U option =
    match cache with
        | [] -> None
        | head::tail -> if functor (fst head) then Some(snd head) else probe_cache_f tail functor
let rec probe_cache (cache:Cache<'T,'U>) (some:'T) : 'U option= 
    probe_cache_f cache (same_x some)



//-----------------------------------------
type DFA = 
    |Empty
    |Regular of bool*DFA array

    static member single(final:bool, i:int) : DFA =
        Regular (final, [|for _ in 1..i -> Empty|])

    member this.set(index:int, d:DFA) : unit =
        match this with
            |Empty -> failwith "Can't be called on an Empty"
            |Regular (_, edges) ->
                Array.set edges index d

    //O(n)
    member this.interpreter_expression<'T when 'T: equality>(input: 'T list, alphabet: 'T list) :bool=
        match this with
            |Empty -> false
            |Regular (end_state, tf) ->
                match input with
                    | [] -> end_state
                    | head::tail -> 
                        let index = (List.findIndex (fun(x)-> x=head) alphabet) 
                        tf.[index].interpreter_expression(tail,alphabet) 
        

type NFA = 
    |Empty
    |Regular of bool*(NFA list)array

    //Return all the states, which are reachable through doing nothing (Epsilon-reachable)
    member this.epsilon_reachable(cache:Cache<NFA, NFA list>, marker:Cache<NFA,unit>) =
        let mark = probe_cache marker this
        if mark.IsSome then ([],cache,marker) else
        let probe = probe_cache cache this
        if probe.IsSome then (unwrap probe,cache,marker) else
        let marker = (this,())::marker
        let arr = match this with |Regular (_,arr)->arr |_-> failwith "Not expecting this here!"
        let my_closure = [this]@arr.[0]
        let rec call_recursivly(cache, marker, set:NFA list) =
            match set with
                | [] -> (cache, marker, [])
                | head::tail ->
                    let (eps, cache,marker) = head.epsilon_reachable(cache,marker)
                    let (cache,marker, app) = call_recursivly(cache,marker,tail)
                    (cache, marker, eps@app)
        let (cache,marker,app) = call_recursivly(cache,marker,arr.[0])
        let res = make_set (my_closure@app)
        let cache = (this,res)::cache
        (res,cache,marker)

    static member single(final:bool,i:int) :NFA =
        Regular(final, [|for _ in 1..i-> []|])

    member this.is_final() : bool =
        match this with |Empty -> failwith "Dont call this on an Empty" |Regular (a, _) -> a

    member this.append(index:int, n:NFA) : unit=
        match this with
            |Empty -> failwith "Can't be called on an Empty"
            |Regular (_,edges) -> 
                let before = Array.get edges index;
                Array.set edges index (n::before)
                ()

    //Possibly O(2^n)? Still pretty fast thanks to chaching and Referecne equality check.
    member this.convert_to_dfa<'T when 'T: equality>(alphabet: 'T list) : DFA =
        let is_final(state: NFA list) = contains state (fun(x) -> x.is_final())
        let find_functor = fun(x) -> 
            let (_,(_,visited)) = x 
            not visited
        let probe_transition_table(tt, set:NFA list) =
            probe_cache_f tt (fun(x) -> set_equals x set)
        let len = List.length alphabet
        let e_cache:Cache<NFA,NFA list> = [] //epsilon cache
        let transition_table:Cache<NFA list, (DFA*bool)> = [] //transition table of our DFA
        let (q_0, e_cache, _) = this.epsilon_reachable(e_cache, [])
        let d_0 = DFA.single(is_final q_0,len)
        let transition_table = (q_0, (d_0,false))::transition_table
        let rec inner(e_cache, transition_table) =
            //Step 1. Pop unvisited element from task queue
            let unvisited = List.tryFind find_functor transition_table
            if unvisited.IsNone then (e_cache,transition_table) else
            let unvisited&(nfas, (dfa:DFA,_)) = unwrap unvisited
            //Step 2. Remove ourself from transition table and add back in, marked as visited
            let transition_table = (nfas, (dfa, true))::(List.filter (not << (same_x unvisited)) transition_table)
            let rec traverse_alphabet_at(e_cache, nfas:NFA list, at:int) =
                match nfas with
                    |[] -> (e_cache, [])
                    | head::tail ->
                        let symbol_transitions = match head with |Regular (_, arr)-> arr.[at+1] |_ -> failwith "Don't expect an empty here!"
                        let rec collect_eps_transitions(e_cache,sym_list:NFA list) =
                            match sym_list with
                                | [] -> (e_cache, [])
                                | head::tail ->
                                    let (eps_trans,e_cache,_) = head.epsilon_reachable(e_cache,[])
                                    let (e_cache, app) = collect_eps_transitions(e_cache,tail)
                                    (e_cache, set_union eps_trans app)
                        let (e_cache,eps_transitions) = collect_eps_transitions(e_cache,symbol_transitions)
                        let (e_cache, rest_set) = traverse_alphabet_at(e_cache,tail,at)
                        (e_cache, set_union (set_union eps_transitions symbol_transitions) rest_set)
            let rec traverse_nfas(e_cache,transition_table, curr:int) =
                if curr >= len then (e_cache,transition_table) else
                let (e_cache,possible_transition) = traverse_alphabet_at(e_cache,nfas,curr)
                let probe = probe_transition_table(transition_table, possible_transition)
                if probe.IsNone then
                    let dfa_n = DFA.single(is_final possible_transition,len)
                    dfa.set(curr, dfa_n)
                    let transition_table = (possible_transition, (dfa_n, false))::transition_table
                    traverse_nfas(e_cache,transition_table,curr+1)
                else
                    let (dfa2,_) = unwrap probe
                    dfa.set(curr, dfa2)
                    traverse_nfas(e_cache,transition_table,curr+1)
            //Step 2. For each input symbol, traverse all the possible transitions of the NFAs
            let (e_cache, transition_table) = traverse_nfas(e_cache,transition_table,0)
            inner (e_cache, transition_table)

        inner(e_cache, transition_table) |> ignore
        d_0
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

    //O(n) Step 1 of ByteCode Interpreter -> Regex->NFA (fast)
    member this.convert_to_nfa<'T when 'T:equality>(alphabet: 'T list, final_flag:bool) : NFA * NFA =
        let len = 1+List.length alphabet
        match this with
            |Epsilon|Empty -> failwith "No valid Regex should contain those Leafs"
            |Literal l -> 
                let curr_state = NFA.single(false, len)
                let index = 1+List.findIndex (fun(x)-> x=l) alphabet;
                let final = NFA.single(final_flag, len)
                curr_state.append(index, final)
                (curr_state,final)
            |Cons (e1, e2) ->
                let (n1,n1end) = e1.convert_to_nfa(alphabet,false)
                let (n2,n2end) = e2.convert_to_nfa(alphabet,final_flag)
                n1end.append(0,n2)
                (n1, n2end)
            | Alternative (e1, e2) ->
                let (n1, n1end) = e1.convert_to_nfa(alphabet, false)
                let (n2, n2end) = e2.convert_to_nfa(alphabet, false)
                let curr = NFA.single(false, len)
                let ende = NFA.single(final_flag, len)
                curr.append(0, n1)
                curr.append(0, n2)
                n1end.append(0, ende)
                n2end.append(0, ende)
                (curr, ende)
            | Star e1 ->
                let (n1, n1end) = e1.convert_to_nfa(alphabet, false)
                n1end.append(0, n1)
                let curr = NFA.single(false, len)
                let ende = NFA.single(final_flag, len)
                curr.append(0, n1)
                curr.append(0, ende)
                n1end.append(0, ende)
                (curr, ende)
            | Plus e1 ->
                Cons(e1, Star e1).convert_to_nfa(alphabet, final_flag)
            | QMark e1 ->
                let (n1, n1end) = e1.convert_to_nfa(alphabet, false)
                let curr = NFA.single(false, len)
                curr.append(0, n1)
                let ende = NFA.single(final_flag, len)
                curr.append(0, ende)
                n1end.append(0, ende)
                (curr, ende)

    //Pure interpreter of regex
    member this.interpret_expression<'T when 'T: equality>(input: 'T list): bool =
        match input with
            | [] -> this.nullable()
            | head::tail -> this.divide(head).interpret_expression(tail)

    //Helper for interpreter of regex
    member this.divide<'T when 'T : equality>(l: 'T) : Expression<'T> = 
        match this with
            |Epsilon|Empty -> Empty
            |Literal other -> if other = l then Epsilon else Empty
            |Cons (e1, e2) -> if e1.nullable() then Alternative(Cons(e1.divide(l),e2),e2.divide(l)) else Cons(e1.divide(l), e2)
            |Alternative (e1, e2) -> Alternative(e1.divide(l), e2.divide(l))
            |Star e1 -> Cons(e1.divide(l), Star e1)
            |Plus e1 -> Cons(e1.divide(l), Star e1)
            |QMark e1 -> e1.divide(l)

    //Helper for interpreter of regex
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

    //Pretty print of self
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

//Tokenizer of possibly invalid strings
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

//Helper method for removing single chars out of a string
let remove_symbol(s:String, sym:Char):String = 
    String.collect (fun(x) -> if x <> sym then x.ToString() else "") s

//Takes a valid sequence of Literals as a String and converts them to a 'T list
let rec tokenize<'T when 'T:> IComparable<String> and 'T:equality>(input: String, alphabet: 'T list): 'T list =
    if input.Length = 0 then [] else 
    let (expr, rest) = scan_forward(input, alphabet)
    match expr with
        |Some (Literal l) -> l::(tokenize(rest, alphabet))
        | _ -> failwith "Illegal input string!"

type Regex<'T when 'T :> IComparable<String> and 'T:equality> = 
    { expression: Expression<'T>; alphabet : 'T list}

    member this.to_string (): String =
        (sprintf "<Regex with \nAlphabet : %A\nExpression : %s\n>" this.alphabet ((0) |> this.expression.to_string))


    member this.generate_acceptor() : String->bool =
        fun(x) ->
            let tokens = tokenize(x, this.alphabet)
            (fst (this.expression.convert_to_nfa(this.alphabet, true))).convert_to_dfa(this.alphabet).interpreter_expression(tokens, this.alphabet)
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
let escape_symbols = ["(";")";"Ø";"*";"|";"+";"?";"·"]

let interpreter(regex:String, input:String) :bool= 
    //First infer alphabet
    let input = String.collect (fun(x) -> if List.contains (x.ToString()) escape_symbols then "\\"+x.ToString() else x.ToString()) input
    printfn "Interpreting Regex: %s with input: %s" regex input
    let alphabet = infer_alphabet input
    printfn "Inferred alphabet: %A" alphabet
    let regex = Regex.parse (regex, alphabet)
    let regex = match regex with |Ok reg -> reg | Error msg -> failwith "Couldn't parse regex"
    printfn "Parsed Regex:\n %s" (regex.to_string())
    regex.expression.interpret_expression(tokenize (input, alphabet))

let bytecode_interpreter(regex:String, input:String) : bool =
    let input = String.collect (fun(x) -> if List.contains (x.ToString()) escape_symbols then "\\"+x.ToString() else x.ToString()) input
    printfn "Interpreting Regex: %s with input: %s" regex input
    let alphabet = infer_alphabet input
    printfn "Inferred alphabet: %A" alphabet
    let regex = Regex.parse (regex, alphabet)
    let regex = match regex with |Ok reg -> reg | Error msg -> failwith "Couldn't parse regex"
    printfn "Parsed Regex:\n %s" (regex.to_string())
    regex.generate_acceptor() input

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
    printfn "Testing direct interpreter"
    printfn "Is in language: %A" (interpreter ("b(a|b)*a", "bbaba"))
    printfn "Is in language: %A" (interpreter ("(b(cb|aa*)c)*","bcbcbabc"))
    printfn "Is in language: %A" (interpreter ("(a|b)*b(a|b)(b|a)","ababbbaba"))
    printfn "Is in language: %A" (interpreter ("((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*","aabaabaabaabaabaabaabaabaabaab"))

let bytecodeinterpreter_tests() : unit =
    printfn "\n---------------------------------------------\n"
    printfn "Testing Bytecode generator (and directly intpreting one string)"
    printfn "Is in language: %A" (bytecode_interpreter ("b(a|b)*a", "bbaba"))
    printfn "Is in language: %A" (bytecode_interpreter ("(b(cb|aa*)c)*","bcbcbabc"))
    printfn "Is in language: %A" (bytecode_interpreter ("(a|b)*b(a|b)(b|a)","ababbbaba"))
    printfn "Is in language: %A" (bytecode_interpreter ("(a|b)?abb*","ab"))
    printfn "Is in language: %A" (bytecode_interpreter ("a*ba*|b*ab*","aba"))
    printfn "Is in language: %A" (bytecode_interpreter ("((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*","aab"))
    printfn "Is in language: %A" (bytecode_interpreter ("((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*((aa)*b(aa)*|a(aa)*ba(aa)*)((aa)*b(aa)*b(aa)*|(aa)*ba(aa)*ba(aa)*|a(aa)*b(aa)*ba(aa)*|a(aa)*ba(aa)*b(aa)*)*","aabaabaabaabaabaabaabaabaabaab"))
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
    bytecodeinterpreter_tests()
    0
