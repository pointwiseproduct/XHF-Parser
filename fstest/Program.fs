﻿open System
open System.IO
open System.Collections.Generic

module Data = begin
    type Block =
        | BlockNull
        | Block of Item list

    and Item =
        | ItemNull
        | ItemFieldPair of FieldPair
        | ItemSingleText of SingleText
        | ItemDict of DictBlock
        | ItemArray of ArrayBlock
        | ItemSpecialExpr of SpecialExpr

    and DictKey =
        | DictKeyNull
        | DictKeyFieldName of FieldName
        | DictKeySingleText of SingleText
        | DictKeyDict of DictBlock
        | DictKeyArray of ArrayBlock
        | DictKeySpecialExpr of SpecialExpr

    and DictItem =
        | DictItemNull
        | DictItemFieldValue of FieldValue
        | DictItemSingleText of SingleText
        | DictItemDict of DictBlock
        | DictItemArray of ArrayBlock
        | DictItemSpecialExpr of SpecialExpr

    and FieldPair = 
        | FieldPairNull
        | FieldPair of FieldName * FieldValue

    and FieldName =
        | FieldNameNull
        | FieldName of string * FieldSubscript list

    and FieldSubscript =
        | FieldSubscript of string

    and FieldValue =
        | FieldValueNull
        | FieldTextPayload of TextPayload
        | FieldDict of DictBlock
        | FieldArray of ArrayBlock
        | FieldSpecial of SpecialExpr

    and SingleText = TextPayload

    and TextPayload =
        | TextPayloadNull
        | Trimmed of string list
        | Verbatim of string list

    and TrimmedText = string list
    and VerbatimText = string list

    and DictBlock = Dictionary<DictKey, DictItem>
    and ArrayBlock = Item list

    and SpecialExpr = KnownSpecials
    and KnownSpecials = string
end;;

module Parser = begin
    // --------
    let subToken (str:string) (s:int) (r:int) = ((str.[s..(r - 1)]), r, true)

    // --------
    let failedToken (s:int) = ("", s, false)

    // --------
    // rev
    let rec reverse<'T> (ts:'T list) =
        match ts with
            | a :: rest -> (reverse<'T> rest) @ [a]
            | [] -> []

    // --------
    let existList (fs:(string -> int -> string * int * bool) list) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let rec g list =
                match list with
                    | f :: tail ->
                        let (tu, ts, res) = f str s
                        if not res then
                            g tail
                        else (tu, ts, true)
                    | [] -> failedToken s
            g fs

    // --------
    // fのinf以上sup以下の繰り返し
    let repeatInfSup (inf:int) (sup:int) (f:string -> int -> string * int * bool) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable i = 0
            let mutable r = s
            let rec g() =
                if i > sup then failedToken s else
                    if r >= str.Length
                    then
                        if inf <= i
                        then subToken str s r
                        else (str.[s..str.Length], str.Length, false)
                    else
                        let (tu, ts, res) = f str r
                        if res then
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
    let repeatInf (inf:int) (f:string -> int -> string * int * bool) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable i = 0
            let mutable r = s
            let rec g() =
                if r >= str.Length
                then
                    if inf <= i
                    then subToken str s r
                    else (str.[s..str.Length], str.Length, false)
                else
                    let (tu, ts, res) = f str r
                    if res then
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
    let repeatSup (sup:int) (f:string -> int -> string * int * bool) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable i = 0
            let mutable r = s
            let rec g() =
                if i > sup then failedToken s else
                    if r >= str.Length
                    then
                        subToken str s r
                    else
                        let (tu, ts, res) = f str r
                        if res then
                            i <- i + 1
                            r <- ts
                            g()
                        else subToken str s r
            g()

    // --------
    // fの0回以上の繰り返し
    let ast (f:string -> int -> string * int * bool) (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            let mutable r = s
            let rec g() =
                if r >= str.Length then subToken str s r
                else
                    let (tu, ts, res) = f str r
                    if res then
                        r <- ts
                        g()
                    else subToken str s r
            g()

    // --------
    // fの0回以上の繰り返し
    let pls (f:string -> int -> string * int * bool) (str:string) (s:int) = repeatInf 1 f str s

    // --------
    // 連結パーシングの例外
    exception ConcatenationFailed

    // --------
    // concatenation
    // (next parser)
    let (>>>) (str:string, s:int, t:int) (f:string -> int -> string * int * bool) =
        let (tu, ts, res) = f str s
        if not res then raise ConcatenationFailed
        else (str, ts, t)

    // --------
    // concatenation
    // (proccess intruding)
    let (>--) (str:string, s:int, t:int) ((f:string -> int -> string * int * bool), g:string -> unit) =
        let (tu, ts, res) = f str s
        if not res then raise ConcatenationFailed
        else
            g tu
            (str, ts, t)

    // --------
    // concatenation
    // (stop concat)
    let (<->) (str:string, s:int, t:int) () =
        (str, s, true)

    // --------
    // extractParserContext
    let evalAndProc (f:string -> int -> (string * int * bool)) (acc:string -> unit) (str:string) (s:int) =
        let (t, u, res) = f str s
        if res then acc t else ()
        (t, u, res)

    let evalAndProcT<'T> (f:string -> int -> ((string * int * bool) * 'T)) (acc:'T -> unit) (str:string) (s:int) =
        let ((a, b, res), t) = f str s
        if res then acc t else ()
        (a, b, res)

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
            if f str.[s]
            then subToken str s (s + 1)
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
                let mutable (tu, ts, res) = ast NONNL str r
                if not res then failedToken s
                else if isNL str.[ts]
                    then subToken str s (ts + 1)
                    else failedToken s
            else failedToken s

    // --------
    // known-specials
    let knownSpecials (str:string) (s:int) =
        if s >= str.Length then failedToken s else
            if str.[s] = '#'
            then let (ru, rs, res) = (existList [matchStr "null"; matchStr "undef"] str (s + 1))
                 if rs = (s + 1)
                 then failedToken s
                 else subToken str s rs
            else failedToken s

    // --------
    // special-expr
    let specialExpr (str:string) (s:int) =
        if s >= str.Length then (failedToken s, "") else
        try
            let mutable special = ""
            let temp =
                (str, s, s)
                >>> (matchStr "=")
                >>> SPTAB
                >-- (knownSpecials, (fun a -> special <- a))
                >>> NL
                <-> ()
            (temp, special)
        with
            | ConcatenationFailed -> (failedToken s, "")
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
        let (t, u, res) =
            (str, s, s)
            >-- (pls NONNL, (fun str -> tx <- str))
            <-> ()
        (tx, u, res)
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
                (fun a b ->
                    try
                        (a, b, b)
                        >>> NL
                        >-- (SPTAB, (fun str -> tx <- ("\n" + str) :: tx))
                        <-> ()
                    with
                        | ConcatenationFailed -> failedToken b
                        | _ -> reraise ()
                )
            ]))
            <-> ()
        (temp, Data.Trimmed (reverse tx))
        with
            | ConcatenationFailed -> (failedToken s, Data.Trimmed [])
            | _ -> reraise ()

    // --------
    // verbatim-text
    let verbatimText (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.Verbatim []) else
        try
        let mutable tx:string list = []
        let temp =
            (str, s, s)
            >>> NL
            >>> (ast (existList [
                evalAndProc partialText (fun str ->
                                            if str.[0] <> ' '
                                            then tx <- str :: tx
                                            else tx <- str.[1..(str.Length - 1)] :: tx);
                (fun a b ->
                    try
                        (a, b, b)
                        >>> NL
                        >>> SPTAB
                        <-> ()
                    with
                        | ConcatenationFailed -> failedToken b
                        | _ -> reraise ())
            ]))
            <-> ()
        (temp, Data.Verbatim (reverse tx))
        with
            | ConcatenationFailed -> (failedToken s, Data.Verbatim [])
            | _ -> reraise ()

    // --------
    // text-payload
    let textPayload (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.TextPayloadNull) else
        try
            let mutable payload:Data.TextPayload = Data.TextPayloadNull
            let temp =
                (str, s, s)
                >>> (existList [
                    evalAndProcT trimmedText (fun a -> payload <- a);
                    evalAndProcT verbatimText (fun a -> payload <- a)
                ])
                >>> NL
                <-> ()
            (temp, payload)
        with
            | ConcatenationFailed -> (failedToken s, Data.TextPayloadNull)
            | _ -> reraise ()

    // -------
    // xhfBlock
    let rec xhfBlock (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.BlockNull) else
        try
            let mutable i = s
            let mutable block:Data.Item list = []
            let mutable temp:string * int * bool = ("", s, false)
            let rec g () =
                let (tu, ts, tb) =
                    (str, i, i)
                    >>> (pls (evalAndProcT xhfItem (fun a -> if a <> Data.ItemNull then block <- a :: block else ())))
                    <-> ()
                if not tb
                then raise ConcatenationFailed
                else if ts <> str.Length
                then
                    let (su, ss, sb) =
                        (str, ts, ts)
                        >>> pls NL
                        <-> ()
                    i <- ss;
                    g ()
                else temp <- (tu, ts, tb)
            g ()
            (temp, Data.Block (reverse block))
        with
            | ConcatenationFailed -> (failedToken s, Data.BlockNull)
            | _ -> reraise ()

    // -------
    // xhfItem
    and xhfItem (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.ItemNull) else
        try
            let mutable item = Data.ItemNull
            let temp =
                (str, s, s)
                >>> (existList [
                    evalAndProcT fieldPair (fun a -> item <- Data.ItemFieldPair a);
                    evalAndProcT singleText (fun a -> item <- Data.ItemSingleText a);
                    evalAndProcT dictBlock (fun a -> item <- Data.ItemDict a);
                    evalAndProcT arrayBlock (fun a -> item <- Data.ItemArray a);
                    evalAndProcT specialExpr (fun a -> item <- Data.ItemSpecialExpr a);
                    comment
                ])
                <-> ()
            (temp, item)
        with
            | ConcatenationFailed -> (failedToken s, Data.ItemNull)
            | _ -> reraise ()

    // --------
    // field-pair
    and fieldPair (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.FieldPairNull) else
        try
            let mutable name:Data.FieldName = Data.FieldNameNull
            let mutable value:Data.FieldValue = Data.FieldValueNull
            let temp =
                (str, s, s)
                >>> evalAndProcT fieldName (fun a -> name <- a)
                >>> evalAndProcT fieldValue (fun a -> value <- a)
                <-> ()
            (temp, Data.FieldPair (name, value))
        with
            | ConcatenationFailed -> (failedToken s, Data.FieldPairNull)
            | _ -> reraise ()

    // --------
    // field-value
    and fieldValue (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.FieldValueNull) else
        try
            let mutable value:Data.FieldValue = Data.FieldValueNull
            let temp =
                (str, s, s)
                >>> (existList [
                    (fun a b ->
                        try
                            (a, b, b)
                            >>> matchStr ":"
                            >>> evalAndProcT textPayload (fun x -> value <- Data.FieldTextPayload x)
                            <-> ()
                        with
                            | ConcatenationFailed -> failedToken b
                            | _ -> reraise ()
                    );
                    evalAndProcT dictBlock (fun a -> value <- Data.FieldDict a);
                    evalAndProcT arrayBlock (fun a -> value <- Data.FieldArray a);
                    evalAndProcT specialExpr (fun a -> value <- Data.FieldSpecial a)
                ])
                <-> ()
            (temp, value)
        with
            | ConcatenationFailed -> (failedToken s, Data.FieldValueNull)
            | _ -> reraise ()

    // --------
    // single-text
    and singleText (str:string) (s:int) = 
        if s >= str.Length then (failedToken s, Data.TextPayloadNull) else
        try
            let mutable payload:Data.SingleText = Data.TextPayloadNull
            let temp =
                (str, s, s)
                >>> matchStr "-"
                >>> (evalAndProcT textPayload (fun a -> payload <- a))
                <-> ()
            (temp, payload)
        with
            | ConcatenationFailed -> (failedToken s, Data.TextPayloadNull)
            | _ -> reraise ()

    // --------
    // dict-block
    and dictBlock (str:string) (s:int) =
        if s >= str.Length then (failedToken s, new Data.DictBlock ()) else
        try
            let mutable dict:Data.DictBlock = new Data.DictBlock ()
            let mutable key:Data.DictKey = Data.DictKeyNull
            let mutable phase = 0
            let temp =
                (str, s, s)
                >>> matchStr "{"
                >>> NL
                >>> (ast (evalAndProcT xhfItem
                    (fun a ->
                        match a with
                        | Data.ItemNull -> ()
                        | Data.ItemFieldPair (Data.FieldPair (p, q)) ->
                            if phase = 0
                            then dict.Add(Data.DictKeyFieldName p, Data.DictItemFieldValue q)
                            else raise ConcatenationFailed
                        | Data.ItemSingleText b ->
                            if phase = 0
                            then phase <- 1; key <- Data.DictKeySingleText b
                            else phase <- 0; dict.Add(key, Data.DictItemSingleText b)
                        | Data.ItemDict b ->
                            if phase = 0
                            then phase <- 1; key <- Data.DictKeyDict b
                            else phase <- 0; dict.Add(key, Data.DictItemDict b)
                        | Data.ItemArray b ->
                            if phase = 0
                            then phase <- 1; key <- Data.DictKeyArray b
                            else phase <- 0; dict.Add(key, Data.DictItemArray b)
                        | Data.ItemSpecialExpr b ->
                            if phase = 0
                            then phase <- 1; key <- Data.DictKeySpecialExpr b
                            else phase <- 0; dict.Add(key, Data.DictItemSpecialExpr b)
                        | _ -> raise ConcatenationFailed
                    )
                ))
                >>> matchStr "}"
                >>> NL
                <-> ()
            if phase <> 0
            then raise ConcatenationFailed
            else ()
            (temp, dict)
        with
            | ConcatenationFailed -> (failedToken s, new Data.DictBlock ())
            | _ -> reraise ()

    // --------
    // array-block
    and arrayBlock (str:string) (s:int) =
        if s >= str.Length then (failedToken s, []) else
        try
            let mutable block:Data.ArrayBlock = []
            let temp =
                (str, s, s)
                >>> matchStr "["
                >>> NL
                >>> (ast (evalAndProcT xhfItem
                    (fun a ->
                        if a <> Data.ItemNull
                        then block <- a :: block
                        else ()
                    )
                ))
                >>> matchStr "]"
                >>> NL
                <-> ()
            (temp, reverse block)
        with
            | ConcatenationFailed -> (failedToken s, [])
            | _ -> reraise ()
end;;

// --------
// ファイルを読み込む
let readFile (path:string) =
    use fileReader = new StreamReader(path)
    let mutable str:string = ""
    while not fileReader.EndOfStream do
        str <- str + fileReader.ReadLine() + "\n"
    str

// --------
let printParser f (str:string) (s:int) =
    let (tu, ts, res) = f str s
    // 左から順に
    //  * パースが完了した時点での文字位置
    //  * パースが正常に終了したならtrue
    //  * パースが終了した位置が入力文字列の長さと一致したならtrue
    printfn "%d:%b:%b" ts res (ts = str.Length)
    ()

[<EntryPoint>]
let main argv =
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "errdiag_1-static.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "errdiag_2-runtime.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "8-newline.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "7-foreach.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "6-entpath.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "5-utf8.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "4-ent.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "3-my.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "2-if.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "db_backed_2_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "db_backed_1_t_basic.inc.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "db_backed_1_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_13_t_1-mkhidden.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_12_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_11_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_10-app.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_10_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_9_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_8_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_7_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_7-app.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_6_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_5_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_4_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_3_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_2_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "basic_1_t_1-basic.txt") 0
    printParser (
        fun a b ->
            let temp = Parser.xhfBlock a b
            fst temp
    ) (readFile "xhf-test.txt") 0
    0 // 整数の終了コードを返します
