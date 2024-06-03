module CopyConstPropFold


(*
    (* An optimisation takes a program and returns a new program. *)
    val optimiseProgram : Fasto.KnownTypes.Prog -> Fasto.KnownTypes.Prog
*)

open AbSyn

(* A propagatee is something that we can propagate - either a variable
   name or a constant value. *)
type Propagatee =
    ConstProp of Value
  | VarProp   of string

type VarTable = SymTab.SymTab<Propagatee>

let rec copyConstPropFoldExp (vtable : VarTable)
                             (e      : TypedExp) =
    match e with
        (* Copy propagation is handled entirely in the following three
        cases for variables, array indexing, and let-bindings. *)
        | Var (name, pos) ->
            let v = SymTab.lookup name vtable
            match v with
                | None -> Var (name, pos)
                | Some (ConstProp ele) -> Constant (ele,pos)
                | Some (VarProp ele) -> Var (ele, pos)
        | Index (name, ei, t, pos) ->
            let i = copyConstPropFoldExp vtable ei
            match i with
                | (Constant(IntVal _, _)) ->
                    Index (name, i, t, pos)
                | _ -> 
                    Index (name, ei, t, pos)
        | Let (Dec (name, ed, decpos), body, pos) ->
            let ed' = copyConstPropFoldExp vtable ed
            match ed' with
                | Var (v, _) ->
                    let newTab = SymTab.bind name (VarProp v) vtable
                    let oBody = copyConstPropFoldExp newTab body
                    oBody
                | Constant (c, _) ->
                    let newTab = SymTab.bind name (ConstProp c) vtable
                    let oBody = copyConstPropFoldExp newTab body
                    oBody
                | Let (Dec (name2, e1, decpos2), e2, pos2) ->
                    // Causes inline-map.fo to fail
                    let newBody = Let (Dec (name, e2, decpos2), body, pos2)
                    let newExp = Let (Dec (name2, e1, decpos), newBody, pos)
                    copyConstPropFoldExp vtable newExp
                | _ -> (* Fallthrough - for everything else, do nothing *)
                    let body' = copyConstPropFoldExp vtable body
                    Let (Dec (name, ed', decpos), body', pos)
        | Times (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal 1, _), _) -> e2'
                | (_, Constant (IntVal 1, _)) -> e1'
                | (Constant (IntVal 0, _), _) -> e1'
                | (_, Constant (IntVal 0, _)) -> e2'
                | (Constant (IntVal x, _), Constant (IntVal y, _)) ->
                    Constant (IntVal (x * y), pos)
                | _ -> Times (e1', e2', pos)
        | And (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (BoolVal x, _), Constant (BoolVal y, _)) -> 
                    Constant (BoolVal (x && y), pos)
                | _ -> And (e1', e2', pos)
        | Constant (x,pos) -> Constant (x,pos)
        | StringLit (x,pos) -> StringLit (x,pos)
        | ArrayLit (es, t, pos) ->
            ArrayLit (List.map (copyConstPropFoldExp vtable) es, t, pos)
        | Plus (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal 0, _), _) -> e2'
                | (_, Constant (IntVal 0, _)) -> e1'
                | (Constant (IntVal x, _), Constant (IntVal y, _)) ->
                    Constant (IntVal (x + y), pos)
                | _ -> Plus (e1', e2', pos)
        | Minus (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (_, Constant (IntVal 0, _)) -> e1'
                | (Constant (IntVal x, _), Constant (IntVal y, _)) ->
                    Constant (IntVal (x - y), pos)
                | _ -> Minus (e1', e2', pos)
        | Equal (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal v1, _), Constant (IntVal v2, _)) ->
                    Constant (BoolVal (v1 = v2), pos)
                | _ ->
                    if false (* e1' = e2' *)  (* <- this would be unsafe! (why?) *)
                    then Constant (BoolVal true, pos)
                    else Equal (e1', e2', pos)
        | Less (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (IntVal v1, _), Constant (IntVal v2, _)) ->
                    Constant (BoolVal (v1 < v2), pos)
                | _ ->
                    if false (* e1' = e2' *)  (* <- as above *)
                    then Constant (BoolVal false, pos)
                    else Less (e1', e2', pos)
        | If (e1, e2, e3, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            match e1' with
                | Constant (BoolVal b, _) ->
                    if b
                    then copyConstPropFoldExp vtable e2
                    else copyConstPropFoldExp vtable e3
                | _ ->
                    If (e1',
                        copyConstPropFoldExp vtable e2,
                        copyConstPropFoldExp vtable e3,
                        pos)
        | Apply (fname, es, pos) ->
            Apply (fname, List.map (copyConstPropFoldExp vtable) es, pos)
        | Iota (en, pos) ->
            Iota (copyConstPropFoldExp vtable en, pos)
        | Length (ea, t, pos) ->
            Length (copyConstPropFoldExp vtable ea, t, pos)
        | Replicate (en, ev, t, pos) ->
            Replicate (copyConstPropFoldExp vtable en,
                       copyConstPropFoldExp vtable ev,
                       t, pos)
        | Map (farg, el, t1, t2, pos) ->
            Map (copyConstPropFoldFunArg vtable farg,
                 copyConstPropFoldExp vtable el,
                 t1, t2, pos)
        | Filter (farg, el, t1, pos) ->
            Filter (copyConstPropFoldFunArg vtable farg,
                    copyConstPropFoldExp vtable el,
                    t1, pos)
        | Reduce (farg, e0, el, t, pos) ->
            Reduce (copyConstPropFoldFunArg vtable farg,
                    copyConstPropFoldExp vtable e0,
                    copyConstPropFoldExp vtable el,
                    t, pos)
        | Scan (farg, e0, el, t, pos) ->
            Scan (copyConstPropFoldFunArg vtable farg,
                  copyConstPropFoldExp vtable e0,
                  copyConstPropFoldExp vtable el,
                  t, pos)
        | Divide (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
            | (Constant (IntVal 0, _), Constant (IntVal y, _)) when y <> 0 ->
                Constant (IntVal 0, pos)
            | (_, Constant (IntVal 1, _)) -> e1'
            | (Constant (IntVal x, _), Constant (IntVal y, _)) when y <> 0 ->
                    Constant (IntVal (x / y), pos)
            | _ -> Divide (e1', e2', pos)
        | Or (e1, e2, pos) ->
            let e1' = copyConstPropFoldExp vtable e1
            let e2' = copyConstPropFoldExp vtable e2
            match (e1', e2') with
                | (Constant (BoolVal false, _), Constant (BoolVal false, _)) ->
                    Constant (BoolVal false, pos)
                | (Constant (BoolVal x, _), Constant (BoolVal y, _)) -> 
                    Constant (BoolVal true, pos)
                | _ -> Or (e1', e2', pos)
        | Not (e0, pos) ->
            let e0' = copyConstPropFoldExp vtable e0
            match e0' with
                | Constant (BoolVal x, _) -> Constant (BoolVal (not x), pos)
                | _ -> Not (e0', pos)
        | Negate (e0, pos) ->
            let e0' = copyConstPropFoldExp vtable e0
            match e0' with
                | Constant (IntVal x, _) -> Constant (IntVal (-x), pos)
                | _ -> Negate (e0', pos)
        | Read (t, pos) -> Read (t, pos)
        | Write (e0, t, pos) -> Write (copyConstPropFoldExp vtable e0, t, pos)

and copyConstPropFoldFunArg (vtable : VarTable)
                            (farg   : TypedFunArg) =
    match farg with
        | FunName fname -> FunName fname
        | Lambda (rettype, paramls, body, pos) ->
            (* Remove any bindings with the same names as the parameters. *)
            let paramNames = (List.map (fun (Param (name, _)) -> name) paramls)
            let vtable'    = SymTab.removeMany paramNames vtable
            Lambda (rettype, paramls, copyConstPropFoldExp vtable' body, pos)

let copyConstPropFoldFunDec = function
    | FunDec (fname, rettype, paramls, body, loc) ->
        let body' = copyConstPropFoldExp (SymTab.empty ()) body
        FunDec (fname, rettype, paramls, body', loc)

let optimiseProgram (prog : TypedProg) =
    List.map copyConstPropFoldFunDec prog
