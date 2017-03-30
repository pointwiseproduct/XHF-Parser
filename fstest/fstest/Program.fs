open System
open System.IO
open System.Collections.Generic

module Data = begin
    type XHF = Block list

    and Block =
        | BlockNull
        | Block of Item list

    and Item =
        | ItemNull
        | ItemFieldPair of FieldPair
        | ItemSingleText of SingleText
        | ItemDict of DictBlock
        | ItemArray of ArrayBlock
        | ItemSpecialExpr of SpecialExpr

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
        | Trimmed of string
        | Verbatim of string

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

    and DictBlock = Dictionary<DictKey, DictItem>
    and ArrayBlock = Item list

    and SpecialExpr = KnownSpecials
    and KnownSpecials = string
end;;

module Semantic = begin
    let checkXHF (data:Data.XHF) =
        let mutable ret: Data.XHF = []
        let checkBlock (block:Data.Block) =
            let mutable dict = new Dictionary<Data.FieldName, Data.FieldValue> ()
            let rec checkItemList (itemList:Data.Item list) =
                let rec f (ts:Data.Item list) =
                    match ts with
                    | a :: rest ->
                        checkItem a
                        f rest
                    | [] ->
                        ()
                f itemList
            and checkItem (item:Data.Item) =
                match item with
                | Data.ItemFieldPair (Data.FieldPair (str, a)) ->
                    if fst (dict.TryGetValue str)
                    then
                        ()
                    else
                        dict.Add (str, a)
                | _ ->
                    ()
            match block with
            | Data.BlockNull ->
                dict
            | Data.Block itemList ->
                checkItemList itemList
                dict
        let rec dropOutFieldPairs (itemList:Data.Item list) =
            match itemList with
            | Data.ItemNull :: rest -> Data.ItemNull :: (dropOutFieldPairs rest)
            | Data.ItemSingleText a :: rest -> Data.ItemSingleText a :: (dropOutFieldPairs rest)
            | Data.ItemDict a :: rest -> Data.ItemDict a :: (dropOutFieldPairs rest)
            | Data.ItemArray a :: rest -> Data.ItemArray a :: (dropOutFieldPairs rest)
            | Data.ItemSpecialExpr a :: rest -> Data.ItemSpecialExpr a :: (dropOutFieldPairs rest)
            | Data.ItemFieldPair a :: rest -> dropOutFieldPairs rest
            | [] -> []
        let rec constructFieldPairs (seq:(Data.FieldName * Data.FieldValue) list) =
            let mutable ret: Data.Item list = []
            let rec f s =
                match s with
                | (a, b) :: rest ->
                    ret <- ret @ [Data.ItemFieldPair (Data.FieldPair (a, b))]
                    f rest
                | [] -> ret
            f seq
        let rec iterateBlock (blockList:Data.Block list) =
            match blockList with
            | (Data.Block a) :: rest ->
                let dict = checkBlock (Data.Block a)
                ret <- ret @ [Data.Block ((dropOutFieldPairs a) @ (constructFieldPairs (Seq.toList (Seq.zip dict.Keys dict.Values))))]
                iterateBlock rest
            | _ :: rest ->
                iterateBlock rest
            | _ ->
                ret
        iterateBlock data
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
    let isANY (ch:char) = true
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
    let ANY = matchOne isANY
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
        if s >= str.Length then (failedToken s, Data.Trimmed "") else
        try
        let mutable tx:string = ""
        let temp =
            (str, s, s)
            >>> SPTAB
            >>> (ast (existList [
                evalAndProc partialText (fun str -> tx <- tx + str);
                (fun a b ->
                    try
                        (a, b, b)
                        >>> NL
                        >-- (SPTAB, (fun str -> tx <- tx + "\n"))
                        <-> ()
                    with
                        | ConcatenationFailed -> failedToken b
                        | _ -> reraise ()
                )
            ]))
            <-> ()
        (temp, Data.Trimmed tx)
        with
            | ConcatenationFailed -> (failedToken s, Data.Trimmed "")
            | _ -> reraise ()

    // --------
    // verbatim-text
    let verbatimText (str:string) (s:int) =
        if s >= str.Length then (failedToken s, Data.Verbatim "") else
        try
        let mutable tx:string = ""
        let temp =
            (str, s, s)
            >>> NL
            >>> (ast (existList [
                evalAndProc partialText (fun str -> tx <- tx + str);
                (fun a b ->
                    try
                        (a, b, b)
                        >>> NL
                        >-- (SPTAB, (fun str -> tx <- tx + "\n"))
                        <-> ()
                    with
                        | ConcatenationFailed -> failedToken b
                        | _ -> reraise ())
            ]))
            <-> ()
        (temp, Data.Verbatim (tx.[1..tx.Length - 1] + "\n"))
        with
            | ConcatenationFailed -> (failedToken s, Data.Verbatim "")
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
        if s >= str.Length then (failedToken s, []) else
        try
            let mutable i = s
            let mutable xhf:Data.XHF = []
            let mutable block:Data.Item list = []
            let mutable temp:string * int * bool = ("", s, false)
            let rec g () =
                let (tu, ts, tb) =
                    (str, i, i)
                    >>> (pls (evalAndProcT xhfItem (fun a -> if a <> Data.ItemNull then block <- a :: block else ())))
                    <-> ()
                if not tb
                then raise ConcatenationFailed
                else
                    if ts <> str.Length
                        then
                            let (su, ss, sb) =
                                (str, ts, ts)
                                >-- (pls NL, (fun _ -> if block <> [] then xhf <- xhf @ [Data.Block block]; block <- [] else ()))
                                <-> ()
                            i <- ss;
                            if i = str.Length
                            then
                                temp <- (tu, str.Length, tb)
                            else
                                g ()
                        else
                            temp <- (tu, ts, tb)
                     
            g ()
            if block <> []
            then xhf <- xhf @ [Data.Block block]
            else ()
            (temp, Semantic.checkXHF xhf)
        with
            | ConcatenationFailed -> (failedToken s, [])
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
        if str.Length > s + 1 && str.[s..s + 1] = "-\n"
        then
            try
                let temp =
                    (str, s, s)
                    >>> matchStr "-"
                    >>> NL
                    <-> ()
                (temp, Data.TextPayloadNull)
            with
                | ConcatenationFailed -> (failedToken s, Data.TextPayloadNull)
                | _ -> reraise ()
        else
            try
                let mutable payload:Data.SingleText = Data.TextPayloadNull
                let temp =
                    (str, s, s)
                    >>> matchStr "-"
                    >>> evalAndProcT textPayload (fun a -> payload <- a)
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

    // --------
    // Parse
    let parse (str:string) =
        let ((_, s, res), data) = xhfBlock str 0
        if res && s = str.Length
        then (true, data)
        else (false, [])
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
let encodeString (str:string) =
    let mutable i = 0
    let mutable out:string = ""
    let rec g () =
        if i >= str.Length
        then ()
        else
            let ch = str.[i]
            i <- i + 1
            if ch = '\n'
            then out <- out + "\\n"; g ()
            else out <- out + string ch; g ()
    g ()
    out

//--------
// 文字列がyattタグかどうか判定する
let testYattTag (str:string) =
    let yatt = "<!yatt:"
    if str.Length >= yatt.Length && str.[0..yatt.Length - 1].Equals(yatt) && str.IndexOf("\n").Equals(-1)
    then
        true
    else
        false

// --------
// 文字列が整数かどうか判定する
let parsingTestInteger (str:string) =
    let mutable f = true
    List.iter (fun (i:int) ->
        f <- f && (
            str.[i].Equals('0') || str.[i].Equals('1') || str.[i].Equals('2') ||
            str.[i].Equals('3') || str.[i].Equals('4') || str.[i].Equals('5') ||
            str.[i].Equals('6') || str.[i].Equals('7') || str.[i].Equals('8') ||
            str.[i].Equals('9')))
        [0..str.Length - 1]
    f

//--------
// 文字列が実数かどうか判定する
let parsingTestReal (str:string) =
    let mutable c = 0
    let mutable f = true
    List.iter (fun (i:int) ->
        match c with
        | 0 ->
            f <- f && (
                str.[i].Equals('0') || str.[i].Equals('1') || str.[i].Equals('2') ||
                str.[i].Equals('3') || str.[i].Equals('4') || str.[i].Equals('5') ||
                str.[i].Equals('6') || str.[i].Equals('7') || str.[i].Equals('8') ||
                str.[i].Equals('9'))
            c <- c + 1
        | 1 ->
            f <- f && (
                str.[i].Equals('0') || str.[i].Equals('1') || str.[i].Equals('2') ||
                str.[i].Equals('3') || str.[i].Equals('4') || str.[i].Equals('5') ||
                str.[i].Equals('6') || str.[i].Equals('7') || str.[i].Equals('8') ||
                str.[i].Equals('9') || str.[i].Equals('.'))
            if str.[i].Equals('.') then c <- c + 1 else ()
        | 2 ->
            f <- f && (
                str.[i].Equals('0') || str.[i].Equals('1') || str.[i].Equals('2') ||
                str.[i].Equals('3') || str.[i].Equals('4') || str.[i].Equals('5') ||
                str.[i].Equals('6') || str.[i].Equals('7') || str.[i].Equals('8') ||
                str.[i].Equals('9'))
            c <- c + 1
        | 3 ->
            f <- f && (
                str.[i].Equals('0') || str.[i].Equals('1') || str.[i].Equals('2') ||
                str.[i].Equals('3') || str.[i].Equals('4') || str.[i].Equals('5') ||
                str.[i].Equals('6') || str.[i].Equals('7') || str.[i].Equals('8') ||
                str.[i].Equals('9'))
        | _ -> raise (Exception())
    ) [0..str.Length - 1]
    f

//--------
// 文字列がバージョン番号かどうか判定する
let parsingTestVersionNum (str:string) =
    let mutable c = 0
    let mutable f = true
    List.iter (fun (i:int) ->
        match c with
        | 0 ->
            f <- f && (
                str.[i].Equals('0') || str.[i].Equals('1') || str.[i].Equals('2') ||
                str.[i].Equals('3') || str.[i].Equals('4') || str.[i].Equals('5') ||
                str.[i].Equals('6') || str.[i].Equals('7') || str.[i].Equals('8') ||
                str.[i].Equals('9'))
            c <- 1
        | 1 ->
            f <- f && (
                str.[i].Equals('0') || str.[i].Equals('1') || str.[i].Equals('2') ||
                str.[i].Equals('3') || str.[i].Equals('4') || str.[i].Equals('5') ||
                str.[i].Equals('6') || str.[i].Equals('7') || str.[i].Equals('8') ||
                str.[i].Equals('9') || str.[i].Equals('.'))
            if str.[i].Equals('.') then c <- 0 else ()
        | _ -> raise (Exception())
    ) [0..str.Length - 1]
    f

// --------
// ファイルに書き込む
let writeToFile (path:string) (content:string) =
    File.WriteAllText (path, content)

exception ToYaml

//--------
// 改行コード付き文字列をstring listに変換
let stringToStringList (str:string) =
    let mutable ts:string list = []
    let rec f (i:int) (s:string) =
        if i = str.Length
        then
            ()
        else
            if str.[i] = '\n'
            then
                ts <- ts @ [s]
                f (i + 1) ("")
            else
                f (i + 1) (s + str.[i].ToString())
    f 0 ""
    ts

//--------
// detection yaml first null
let detectionYamlNull (raw:string) =
    let ts = stringToStringList raw
    let rec f (s:string list) =
        match s with
        | a :: rest ->
            if a.Length > 0 && a.[0] = '#'
            then
                f rest
            else
                if a.Length = 0
                then
                    true
                else
                    false
        | [] -> false
    f ts

// --------
// to yaml
let toYaml (raw:string) (data:Data.XHF) =
    let mutable str = ""
    let mutable indent = 0
    let rec outIndent (i:int) =
        if i = 0 then () else str <- str + "  "; outIndent (i - 1)
    let replaceStr (raw:String) =
        let mutable str = raw
        let rec removeTailSpace () =
            if str.Length > 0 && str.[str.Length - 1] = ' '
            then
                str <- str.[0..str.Length - 2]
                removeTailSpace ()
            else
                ()
        let mutable ret = ""
        removeTailSpace ()
        if str.Length = 0
        then ret <- "''"
        else if testYattTag str
        then ret <- str
        else if parsingTestInteger str
        then ret <- str
        else if str.[str.Length - 1].Equals('\n') && (parsingTestInteger str.[0..str.Length - 2])
        then ret <- "'" + str + "\n'"
        else if parsingTestVersionNum str || str.Equals("~")
        then ret <- "'" + str + "'"
        else
            ret <- str.Replace("\\", "\\\\").Replace("\n", "\\n").Replace("\"", "\\\"")
            if ret.IndexOf('&') >= 0 || ret.IndexOf('!') >= 0 || ret.IndexOf(':') >= 0 ||
               ret.IndexOf(';') >= 0 || ret.[0].Equals('^') || ret.IndexOf('\n') >= 0 ||
               ret.IndexOf('\\') >= 0
            then
                ret <- "\"" + ret + "\""
            else
                ()
        ret
    let rec matchXHF (ts:Data.XHF) =
        match ts with
        | Data.BlockNull :: rest ->
            outIndent indent
            str <- str + "- \n"
            indent <- indent + 1
            matchXHF rest
            indent <- indent - 1
        | Data.Block itemList :: rest ->
            outIndent indent
            str <- str + "- \n"
            indent <- indent + 1
            matchItemList itemList
            indent <- indent - 1
            matchXHF rest
        | [] -> ()
    and matchItemList (ts:Data.Item list) =
        match ts with
        | a :: rest ->
            outIndent indent
            matchItem a
            matchItemList rest
        | [] -> ()
    and matchItem (data:Data.Item) =
        match data with
        | Data.ItemFieldPair a ->
            matchFieldPairInList a
        | Data.ItemSingleText a ->
            matchTextPayload a
        | Data.ItemDict a ->
            matchDict a
        | Data.ItemArray a ->
            matchArray a
        | Data.ItemSpecialExpr a ->
            matchSpecialExpr a
        | _ -> raise ToYaml
    and matchFieldPairInList (data:Data.FieldPair) =
        match data with
        | Data.FieldPair (name, ts) ->
            matchFieldNameInList name
            str <- str + ": "
            matchFieldValueInList ts
        | _ -> raise ToYaml
    and matchFieldNameInList (name:Data.FieldName) =
        match name with
        | Data.FieldName (name, []) ->
            str <- str + name
        | Data.FieldName (name, ts) ->
            let listProc (ss:Data.FieldSubscript list) = 
                match ss with
                | Data.FieldSubscript s :: rest -> str <- str + s + ", ";
                | []        -> str <- str.[0..str.Length - 3]
            str <- str + "- " + name + "[";
            listProc ts
            str <- str + "]\n"
        | _ -> raise ToYaml
    and matchFieldValueInList (data:Data.FieldValue) =
        match data with
        | Data.FieldTextPayload a ->
            matchTextPayload a;
        | Data.FieldDict a ->
            matchDict a;
        | Data.FieldArray a ->
            matchArray a;
        | Data.FieldSpecial a ->
            matchSpecialExpr a;
        | _ -> raise ToYaml
    and matchFieldPairInDict (data:Data.FieldPair) =
        match data with
        | Data.FieldPair (name, ts) ->
            matchFieldNameInDict name
            indent <- indent + 1
            matchFieldValueInDict ts
            indent <- indent - 1
        | _ -> raise ToYaml
    and matchFieldNameInDict (name:Data.FieldName) =
        match name with
        | Data.FieldName (name, []) ->
            str <- str + name + ": "
        | Data.FieldName (name, ts) ->
            let listProc (ss:Data.FieldSubscript list) = 
                match ss with
                | Data.FieldSubscript s :: rest -> str <- str + s + ", ";
                | []        -> str <- str.[0..str.Length - 3]
            str <- str + name + "[";
            listProc ts
            str <- str + "]: "
        | _ -> raise ToYaml
    and matchFieldValueInDict (data:Data.FieldValue) =
        match data with
        | Data.FieldTextPayload a ->
            matchTextPayload a;
        | Data.FieldDict a ->
            matchDict a;
        | Data.FieldArray a ->
            matchArray a;
        | Data.FieldSpecial a ->
            matchSpecialExpr a;
        | _ -> raise ToYaml
    and matchTextPayload (text:Data.TextPayload) =
        match text with
        | Data.Trimmed s  ->
            str <- str + (replaceStr s)
        | Data.Verbatim s ->
            str <- str + (replaceStr s)
        | Data.TextPayloadNull ->
            str <- str + "''"
        str <- str + "\n"
    and matchDict (data:Data.DictBlock) =
        let rec matchDictList (ts:(Data.DictKey * Data.DictItem) list) =
            match ts with
            | (a, b) :: rest ->
                indent <- indent + 1
                outIndent indent
                matchDictKey a
                matchDictItem b
                indent <- indent - 1
                matchDictList rest
            | [] -> ()
        str <- str + "\n"
        matchDictList (Seq.toList (Seq.zip data.Keys data.Values))
    and matchDictKey (data:Data.DictKey) =
        match data with
        | Data.DictKeyNull -> raise ToYaml
        | Data.DictKeyFieldName a ->
            matchFieldNameInDict a
        | Data.DictKeySingleText a ->
            matchTextPayload a
        | Data.DictKeyDict a ->
            matchDict a
        | Data.DictKeyArray a ->
            matchArray a
        | Data.DictKeySpecialExpr a ->
            matchSpecialExpr a
    and matchDictItem (data:Data.DictItem) =
        match data with
        | Data.DictItemNull -> raise ToYaml
        | Data.DictItemFieldValue a ->
            matchFieldValueInDict a
        | Data.DictItemSingleText a ->
            matchTextPayload a
        | Data.DictItemDict a ->
            matchDict a
        | Data.DictItemArray a ->
            matchArray a
        | Data.DictItemSpecialExpr a ->
            matchSpecialExpr a
    and matchArray (data:Data.ArrayBlock) =
        if data.Length.Equals(0)
        then
            str <- str + "[]\n\n"
        else
            str <- str + "\n"
            indent <- indent + 1
            let rec f (l:Data.ArrayBlock) =
                match l with
                | a :: tail ->
                    outIndent indent
                    str <- str + "- "
                    matchArrayItem a
                    f tail
                | [] -> ()
            f data
            indent <- indent - 1
    and matchArrayItem (data:Data.Item) =
        match data with
        | Data.ItemFieldPair (Data.FieldPair (x, y)) ->
            matchFieldNameInArray x
            str <- str + "\n"
            outIndent indent
            str <- str + "- "
            matchFieldValueInDict y
        | _ -> matchItem data
    and matchFieldNameInArray (name:Data.FieldName) =
        match name with
        | Data.FieldName (name, []) ->
            str <- str + (replaceStr name)
        | Data.FieldName (name, ts) ->
            let rec listProc (ss:Data.FieldSubscript list) = 
                match ss with
                | Data.FieldSubscript s :: rest ->
                    str <- str + s + ", "
                    listProc rest
                | []        ->
                    str <- str.[0..str.Length - 3]
            str <- str + name + "[";
            listProc ts
            str <- str + "] "
        | _ -> raise ToYaml
    and matchSpecialExpr (data:Data.KnownSpecials) =
        str <- str + "~\n"
    let makeStrList (str:string) =
        let mutable ts:string list = []
        let mutable current: string = ""
        String.iter (fun c -> if c.Equals('\n') then ts <- ts @ [current]; current <- "" else current <- current + c.ToString()) str
        ts
    let countSegments (lines:string list) =
        let mutable count = 0
        let rec innerCount (lines:string list) =
            match lines with
            | a :: rest ->
                if a.Length >= 3 && not (a.[2].Equals(' '))
                then
                    count <- count + 1
                else
                    ()
                innerCount rest
            | [] -> count
        innerCount lines
    matchXHF data
    if detectionYamlNull raw
    then
        str <- "--- \n- ~\n" + str
    else
        str <- "--- \n" + str
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
    let raw = (readFile argv.[0])
    let temp = Parser.xhfBlock (readFile argv.[0]) 0
    printfn "%s" (toYaml raw (snd temp))

    //printParser (
    //    fun a b ->
    //        let temp = Parser.xhfBlock a b
    //        writeToFile "yaml/debug.txt" (toYaml a (snd temp))
    //        fst temp
    //) (readFile "debug.txt") 0

    0
