﻿open System
open System.IO
open System.Collections.Generic

module Data = begin
    type Block = Item list

    and Item =
        | ItemFieldPair of FieldPair
        | ItemSingleText of SingleText
        | ItemDict of DictBlock
        | ItemArray of ArrayBlock
        | ItemSpecialExpr of SpecialExpr

    and FieldPair = FieldName * FieldValue
    and FieldName =
        | FieldName of string * FieldSubscript list

    and FieldSubscript =
        | FieldSubscript of string

    and FieldValue =
        | FieldTextPayload of TextPayload
        | FieldDict of DictBlock
        | FieldArray of ArrayBlock
        | FieldSpecial of SpecialExpr

    and TextPayload =
        | Trimmed of string list
        | Verbatim of string list

    and TrimmedText = string list
    and VerbatimText = string list
    and SingleText = TextPayload

    and DictBlock = Dictionary<FieldName, FieldValue>
    and ArrayBlock = Item list

    and SpecialExpr = KnownSpecials
    and KnownSpecials = string

    let specialDataNull:KnownSpecials = "null"
end;;

module Parser = begin
    // --------
    let subToken (str:string) (s:int) (r:int) = ((str.[s..(r - 1)]), r)

    // --------
    let failedToken (s:int) = ("", s)

    // --------
    // rev
    let rec reverse<'T> (ts:'T list) =
        match ts with
            | a :: rest -> (reverse<'T> rest) @ [a]
            | [] -> []

    // --------
    let existList (fs:(string -> int -> string * int) list) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let rec g list =
                match list with
                | f :: tail ->
                    let (tu, ts) = f str s
                    if ts = s then
                        g tail
                    else (tu, ts)
                | [] -> failedToken s
            g fs

    // --------
    // fのinf以上sup以下の繰り返し
    let repeatInfSup (inf:int) (sup:int) (f:string -> int -> string * int) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable i = 0
            let mutable r = s
            let rec g() =
                if i > sup then failedToken s else
                    if r >= str.Length
                    then
                        if inf <= i
                        then subToken str s r
                        else (str.[s..str.Length], str.Length)
                    else
                        let (tu, ts) = f str r
                        if ts <> r then
                            i <- i + 1
                            r <- ts
                            g()
                        else
                            if inf <= i
                            then subToken str s r
                            else failedToken s
            g()

    // --------
    // fのinf以上の繰り返し
    let repeatInf (inf:int) (f:string -> int -> string * int) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable i = 0
            let mutable r = s
            let rec g() =
                if r >= str.Length
                then
                    if inf <= i
                    then subToken str s r
                    else (str.[s..str.Length], str.Length)
                else
                    let (tu, ts) = f str r
                    if ts <> r then
                        i <- i + 1
                        r <- ts
                        g()
                    else
                        if inf <= i
                        then subToken str s r
                        else failedToken s
            g()

    // --------
    // fのsup以下の繰り返し
    let repeatSup (sup:int) (f:string -> int -> string * int) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable i = 0
            let mutable r = s
            let rec g() =
                if i > sup then failedToken s else
                    if r >= str.Length
                    then
                        subToken str s r
                    else
                        let (tu, ts) = f str r
                        if ts <> r then
                            i <- i + 1
                            r <- ts
                            g()
                        else subToken str s r
            g()

    // --------
    // fの0回以上の繰り返し
    let ast (f:string -> int -> string * int) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable r = s
            let rec g() =
                if r >= str.Length then subToken str s r
                else
                    let (tu, ts) = f str r
                    if ts <> r then
                        r <- ts
                        g()
                    else subToken str s r
            g()

    // --------
    // fの0回以上の繰り返し
    let pls (f:string -> int -> string * int) (str:string) (s:int) = repeatInf 1 f str s

    // --------
    // 連結パーシングの例外
    exception ConcatenationFailed

    // --------
    // concatenation
    // (next parser)
    let (>>>) (str:string, s:int, t:int) (f:string -> int -> string * int) =
        let (tu, ts) = f str s
        if ts = s && ts <> str.Length then raise ConcatenationFailed
        else (str, ts, t)

    // --------
    // concatenation
    // (proccess intruding)
    let (>--) (str:string, s:int, t:int) ((f:string -> int -> string * int), g:string -> unit) =
        let (tu, ts) = f str s
        if ts = s then raise ConcatenationFailed
        else
            g tu
            (str, ts, t)

    // --------
    // concatenation
    // (stop concat)
    let (<->) (str:string, s:int, t:int) () =
        (str, s)

    // --------
    // extractParserContext
    let evalAndProc (f:string -> int -> (string * int)) (acc:string -> unit) (str:string) (s:int) =
        let (t, u) = f str s
        if u <> s then acc t else ()
        (t, u)

    let evalAndProcT<'T> (f:string -> int -> ((string * int) * 'T)) (acc:'T -> unit) (str:string) (s:int) =
        let ((a, b), t) = f str s
        if b <> s then acc t else ()
        (a, b)

    // --------
    // 一致
    let matchStr (u:string) (str:string) (s:int) =
        let mutable r = s
        let mutable i = 0
        let rec g() =
            if i = u.Length then subToken str s r else
            if r >= str.Length then failedToken s else
            if str.[r] = u.[i] then
                r <- r + 1
                i <- i + 1
                g()
            else failedToken s
        g()

    // --------
    let isNL (ch:char) = if ch = '\n' then true else false
    let isNONNL (ch:char) = if ch = '\n' then false else true
    let isSPTAB (ch:char) = " \t".IndexOf ch >= 0
    let isNAME (ch:char) =
        if Char.IsDigit ch
        then true
        else if Char.IsLower ch || Char.IsUpper ch
        then true
        else if ("_.-/~!".IndexOf ch) >= 0
        then true
        else false

    // --------
    let matchOne f (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            if f str.[s] then
                subToken str s (s + 1)
            else failedToken s

    let NL = matchOne isNL
    let NONNL = matchOne isNONNL
    let SPTAB = matchOne isSPTAB
    let NAME = matchOne isNAME

    // --------
    // comment
    let comment (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable r = s
            if str.[r] = '#' then
                r <- r + 1
                let mutable dummy = 0
                let mutable (tu, ts) = ast NONNL str r
                if ts = r then failedToken s
                else if isNL str.[ts] then
                    subToken str s (ts + 1)
                    else failedToken s
            else failedToken s

    // --------
    // known-specials
    let knownSpecials (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            if str.[s] = '#' then
                let (ru, rs) = (existList [matchStr "null"; matchStr "undef"] str (s + 1))
                if rs = (s + 1) then
                    failedToken s
                else subToken str s rs
            else failedToken s

    // --------
    // special-expr
    let specialExpr (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            try
                (str, s, s)
                >>> (matchStr "=")
                >>> SPTAB
                >>> knownSpecials
                >>> NL
                <-> ()
            with
                | ConcatenationFailed -> failedToken s
                | _ -> reraise ()

    // --------
    // field-subscript
    let fieldSubscript (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.FieldSubscript "") else
            try
                let mutable name = ""
                let temp =
                    (str, s, s)
                    >>> (matchStr "[")
                    >-- (ast NAME, (fun str -> name <- str))
                    >>> (matchStr "]")
                    <-> ()
                (temp, Data.FieldSubscript name)
            with
                | ConcatenationFailed -> (failedToken s, Data.FieldSubscript "")
                | _ -> reraise ()

    // --------
    // field-name
    let fieldName (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.FieldName ("", [])) else
        try
            let mutable name = ""
            let mutable subscriptList:Data.FieldSubscript list = []
            let temp =
                (str, s, s)
                >-- (pls NAME, (fun str -> name <- str))
                >>> (ast (evalAndProcT fieldSubscript (fun a -> subscriptList <- a :: subscriptList)))
                <-> ()
            (temp, Data.FieldName (name, reverse subscriptList))
        with
            | ConcatenationFailed -> (failedToken s, Data.FieldName ("", []))
            | _ -> reraise ()

    // --------
    // partial-text
    let partialText (str:string) (s:int) =
        if s >= str.Length then failedToken s else
        try
        let mutable tx = ""
        let (t, u) =
            (str, s, s)
            >-- (pls NONNL, (fun str -> tx <- str))
            <-> ()
        (tx, u)
        with
            | ConcatenationFailed -> failedToken s
            | _ -> reraise ()

    // --------
    // trimmed-text
    let trimmedText (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.Trimmed []) else
        try
        let mutable tx:string list = []
        let temp =
            (str, s, s)
            >>> SPTAB
            >>> (ast (existList [
                evalAndProc partialText (fun str -> tx <- str :: tx);
                (fun a b -> (a, b, b) >>> NL >-- (SPTAB, (fun str -> tx <- ("\n" + str) :: tx)) <-> ())
            ]))
            <-> ()
        (temp, Data.Trimmed (reverse tx))
        with
            | ConcatenationFailed -> (failedToken s, Data.Trimmed [])
            | _ -> reraise ()
end;;

// --------
let printParser f (str:string) (s:int) =
    let (tu, ts) = f str s
    printfn "%d:%s" ts tu
    ()

[<EntryPoint>]
let main argv =
    printParser (
        fun a b ->
            let temp = Parser.trimmedText a b
            fst temp
    )  " \n \n aaa" 0
    printParser (
        fun a b ->
            let temp = Parser.fieldName a b
            fst temp
    )  "abc[hogehoge][piyo]" 0
    printParser (
        fun a b ->
            let temp = Parser.fieldSubscript a b
            fst temp
    )  "[hogehoge]" 0
    printParser (Parser.repeatInfSup 3 5 (Parser.matchStr "a")) "aaaa" 0
    printParser (Parser.repeatInf 3 (Parser.matchStr "a")) "aaaaaa" 0
    printParser (Parser.repeatSup 4 (Parser.matchStr "a")) "aaaaa" 0
    printParser Parser.specialExpr "= #null\n" 0
    printParser Parser.specialExpr "= #nul\n" 0
    printParser Parser.knownSpecials "#undef" 0
    printParser Parser.knownSpecials "#null" 0
    printParser (Parser.existList [Parser.matchStr "null"; Parser.matchStr "undef"]) "null" 0
    printParser (Parser.existList [Parser.matchStr "null"; Parser.matchStr "undef"]) "undef" 0
    printParser (Parser.matchStr "test") "abc" 0
    printParser Parser.comment "#as\n" 0
    0 // 整数の終了コードを返します
