
(*ambiente*)
type 't env = (string * 't) list

exception WrongBindlist

let emptyenv(x) = [("", x)]

let rec applyenv(x, y) = 
  match x with
    | [(_, e)] -> e
    | (i1, e1) :: x1 -> 
        if y = i1 then e1 
        else applyenv(x1, y)
    | [] -> failwith("wrong env")    

let bind(r, l, e) = (l, e) :: r

let rec bindlist(r, il, el) = 
  match (il, el) with
    | ([], []) -> r
    | (i::il1, e::el1) -> bindlist(bind(r, i, e), il1, el1)
    | _ -> raise WrongBindlist;;


(*sintassi linuaggio didattico*)
type ide = string 

type exp = Eint of int
         | Ebool of bool
         (*Aggiunto il tipo stringa per poter effeture delle operazioni anche su di esso*)
         | Estring of string
         | Den of ide
         | Sum of exp * exp
         | Diff of exp * exp
         | Prod of exp * exp
         | Eq of exp * exp
         | Minus of exp
         | Iszero of exp
         | Or of exp * exp
         | And of exp * exp
         | Not of exp
         | Con of exp * exp
         | Ifthenelse of exp * exp * exp
         | Let of ide * exp * exp(* Dichiarazione di ide: modifica ambiente*)
         | Fun of ide (*parametro formale*) * exp(*body*)(* Astrazione di funzione*)
         | Apply of exp * exp (*parametro attuale*)(* Applicazione di funzione*)
         | Letrec of ide(*nome fun*)*ide(*par.formale*)*exp(*body fun*)*exp(*body let*)
         (*dichiarazione del secondo progetto 2018-2019*)
         | My_dict of el
         | Add of exp * ide * exp
         | Show of exp * ide
         | Modify of exp * ide * exp
         | Remove of exp * ide
         | Clear of exp
         | ApplyOver of exp * exp
and el = Empty | DictEl of ((ide * exp) * el)

(*evT*)
type evT= Int of int
        |Bool of bool
        |String of string
        |Unbound
        |RecFunVal of ide * ide * exp * evT env
        |Funval of efun
        |Dictionary of elem 
and elem = EmptyDict | DictElevT of ((ide* evT) * elem)
and efun = ide* exp * evT env;;




(*typechecking dinamico*)
let typecheck(x, y) = match x with
  | "int" ->   
      (match y with 
        | Int(u) -> true
        | _ -> false)
  | "bool" -> 
      (match y with
        |Bool(b) -> true
        |_->false)
  | "string" ->
      (match y with
        | String(str) -> true
        | _ -> false)
  |_->failwith("error");;


(*plus*)
let plus(x, y) = if typecheck("int", x) && typecheck("int", y) then  
    (match (x, y) with 
      |(Int(u), Int(w)) -> Int(u + w)
      |_->failwith("error"))
  else failwith ("error");;


(*diff*)
let diff(x,y)=if typecheck("int",x) && typecheck("int", y) then
    (match (x, y) with 
      |(Int(u), Int(w)) -> Int(u - w)
      |_->failwith("error"))
  else failwith ("type error");;


(*prod*)
let prod(x,y)=if typecheck("int",x) && typecheck("int", y) then
    (match (x, y) with 
      |(Int(u), Int(w)) -> Int(u * w)
      |_->failwith("error"))
  else failwith ("type error");;


(*iszero*)
let iszero(x)=if typecheck("int",x) then
    (match x with
      |Int(u)->if u=0 then Bool(true) else Bool(false)
      |_->failwith("error"))
  else failwith("type error");;


(*eq*)
let equ(x,y)=if typecheck("int",x) && typecheck("int", y) then
    (match (x, y) with 
      |(Int(u), Int(w)) -> if u=w then Bool(true) else Bool(false)
      |_->failwith("error"))
  else failwith ("type error");;


(*minus*)
let minus(x)=if typecheck("int",x) then
    (match x with
      |Int(u)->Int(-u)
      |_->failwith("error"))
  else failwith("type error");;



(*et*)
let et(x,y)=if typecheck("bool",x) && typecheck("bool", y) then
    (match (x, y) with 
      |(Bool(u), Bool(w)) -> Bool(u && w)
      |_->failwith("error"))
  else failwith ("type error");;



(*vel*)
let vel(x,y)=if typecheck("bool",x) && typecheck("bool", y) then
    (match (x, y) with 
      |(Bool(u), Bool(w)) -> Bool(u || w)
      |_->failwith("error"))
  else failwith ("type error");;



(*non*)
let non(x)=if typecheck("bool",x) then
    (match x with 
      |Bool(u) -> Bool(not(u))
      |_->failwith("error"))
  else failwith ("type error");;


(*aggiunta per avere anche delle operazioni su stringhe*)
(*conc*)
let conc(x, y)=if typecheck("string", x) then
    (match (x,y) with
      | (String(a), String(b)) -> String(a^b)
      | _ -> failwith("error"))
  else failwith("Type error")

let rec find((dic:elem), (a:ide)) =
  begin match dic with
    | DictElevT((x, y), ex) -> 
        if(x = a) then
          true
        else
          find(ex, a)
    | EmptyDict -> false
  end;;

let rec lookup((dic: elem), (a:ide)) = 
  begin match dic with
    | DictElevT((x,y), ex) -> 
        if(x = a) then
          y
        else 
          lookup(ex, a)
    | _ -> failwith("Element not found")
  end;;

let rec subst((dic:elem), (a:ide), (b:evT)) =
  begin match dic with
    | DictElevT((x, y), ex) -> 
        if(x = a) then
          DictElevT((x, b), ex)
        else
          DictElevT((x, y), subst(ex, a, b))
    | _ -> failwith("Element not found")
  end;;

let rec rm((dic:elem), (a:ide)) =
  begin match dic with
    | DictElevT((x,y), ex) -> 
        if(x = a) then
          ex
        else 
          DictElevT((x, y), rm(ex, a))
    | _ -> failwith("Element not found")
  end;;


(*interprete linguaggio didattico-scope statico*)
let rec eval ((e: exp), (r: evT env)) =
  begin match e with
    | Eint(n) -> Int(n)
    | Ebool(b) -> Bool(b)
    | Estring(str) -> String(str)
    | Den(i) -> applyenv(r, i)
    | Sum(a, b) ->  plus(eval(a, r), eval(b, r))
    | Diff(a, b)  ->  diff(eval(a, r), eval(b, r))
    | Prod(a,b)->prod(eval(a,r), eval(b,r))
    | Iszero(a) -> iszero(eval(a, r))
    | Eq(a, b) -> equ(eval(a, r),eval(b, r))
    | Minus(a) ->  minus(eval(a, r))
    | And(a, b) ->  et(eval(a, r), eval(b, r))
    | Or(a, b) ->  vel(eval(a, r), eval(b, r))
    | Not(a) -> non(eval(a, r))
    | Con(a, b) -> conc(eval(a, r), eval(b, r))
    | Ifthenelse(a, b, c) -> let g = eval(a, r) in
          if typecheck("bool", g) then
            (if g = Bool(true) then eval(b, r) else eval(c, r))
          else failwith ("nonboolean guard")
    | Let(i, e1, e2) -> eval(e2, bind (r, i, eval(e1, r))) 
    | Fun(i,a) -> Funval(i,a,r)
    | Letrec(f, i, fBody,letBody) -> 
        let benv = 
          bind(r, f, (RecFunVal(f, i, fBody, r)))
        in eval(letBody, benv)
    | Apply(Den f, eArg) -> 
        (let fclosure= eval(Den f, r) in 
           match fclosure with 
             | Funval(arg, fbody, fDecEnv) -> 
                 eval(fbody, bind(fDecEnv, arg, eval(eArg, r))) 
             | RecFunVal(f, arg, fbody, fDecEnv) ->
                 let aVal= eval(eArg, r) in 
                 let rEnv= bind(fDecEnv, f, fclosure) in
                 let aEnv= bind(rEnv, arg, aVal) in 
                   eval(fbody, aEnv)
             | _ -> failwith("non functional value"))
    | Apply(_,_) -> failwith("not function")

    (*Nuovo dizionario*)
    | My_dict(a) -> 
        let rec evalDict ((dic: el), (r: evT env)) =
          begin match dic with
            | Empty -> EmptyDict
            | DictEl((x, y), ex) -> 
                let value = eval(y, r) in
                  DictElevT((x, value), evalDict( ex, r))
          end
        in
          Dictionary(evalDict( a, r))

    (*Inserisce in testa al Dizionario un nuovo elemento a con valore b*)
    | Add(Den dic, a, b) ->
        (let value = eval(b, r)in
         let x = eval(Den dic, r) in
           begin match x with
             | Dictionary(dict) -> Dictionary(DictElevT((a, value), dict))
             | _ -> failwith("Type error")
           end)

    (*Mostra il valore della prima occorrenza dell'elemento a*)
    | Show(Den dic, a) -> 
        (let x = eval(Den dic, r) in
           begin match x with
             | Dictionary(dict) -> lookup(dict, a)
             | _ -> failwith("Key not found")
           end)

    (*Modifica la prima occorrenza dell'elemento a con il valore di b*)
    | Modify(Den dic, a, b) ->
        (let value = eval(b, r) in
         let x = eval(Den dic, r) in
           begin match x with
             | Dictionary(dicti) -> Dictionary(subst(dicti, a, value))
             | _ -> failwith("Type error")
           end)

    (*La Remove elimina la prima occorrenza dell'elemento a*)
    | Remove(Den dic, a) ->
        (let x = eval(Den dic, r) in
           begin match x with
             | Dictionary(dict) -> Dictionary(rm(dict, a))
             | _ -> failwith("Type error")
           end)

    (*restituisce un dizionario vuoto*)
    | Clear(Den dic) -> 
        (let x = eval(Den dic, r) in
           begin match x with
             | Dictionary(dict) -> Dictionary(EmptyDict)
             | _ -> failwith("Type error")
           end
        )

    (*Per l'applicazione di una funzione e' necessario che tutti gli elementi siano dello stesso tipo*)
    | ApplyOver(Den fn, Den dic) ->
        ( let x = eval(Den dic, r) in
          let fclosure = eval(Den fn, r) in
            begin match fclosure, x with
              | Funval(arg, fbody, fDecEnv), Dictionary(dict) ->
                  let rec applyFun(x) =
                    begin match x with
                      | DictElevT((x, y), ex) -> DictElevT((x, eval(fbody, bind(fDecEnv, arg, y))), applyFun(ex))
                      | EmptyDict -> EmptyDict
                    end
                  in
                    Dictionary(applyFun(dict))

              | RecFunVal(f, arg, fbody, fDecEnv), Dictionary(dict) ->
                  let rec applyFun(x) =
                    begin match x with
                      | DictElevT((x, y), ex) -> 
                          let rEnv= bind(fDecEnv, f, fclosure) in
                          let aEnv= bind(rEnv, arg, y) in 
                            DictElevT((x, eval(fbody, aEnv)), applyFun(ex))
                      | EmptyDict -> EmptyDict
                    end
                  in
                    Dictionary(applyFun(dict))

              | _, Dictionary(_) -> failwith("Non functional value")
              | Funval(_), _ -> failwith("Dictionary not accepted")
              | RecFunVal(_), _ -> failwith("Dictionary not accepted")
              | _, _ -> failwith("Illegal argument")
            end
        )
    | _ -> failwith("Something goes wrong")

  end;;


(*Prova della funzione add aggiungendo un elemento*)
eval(Let("ciccio", My_dict(DictEl(("a", Eint 12), Empty)), 
         Add(Den "ciccio", "a", Eint 17)), []);;

(*prova della funzione show che va a cercare l'elemento nel dizionario Ciccio*)
eval(Let("ciccio", My_dict(DictEl(("a", Eint 12), DictEl(("b", Eint 13), Empty))), 
         Show(Den "ciccio", "a")), []);;

(*Prova Modify*)
eval(Let("ciccio", My_dict(DictEl(("a", Eint 12), DictEl(("b", Eint 13), Empty))), 
         Modify(Den "ciccio", "a", Eint 17)), []);;

(*prova Remove*)
eval(Let("ciccio", My_dict(DictEl(("a", Eint 12), DictEl(("b", Eint 13), Empty))), 
         Remove(Den "ciccio", "a")), []);;

(*Prova Clear*)
eval(Let("ciccio", My_dict(DictEl(("a", Eint 12), DictEl(("b", Eint 13), Empty))), 
         Clear(Den "ciccio")), []);;



(*Vari test sulla funzione ApplyOver dove testo in ordine, i buleani, gli interi e le stringhe*)

eval( Let("funzione", Fun("x", Or(Den "x", Ebool true)),
          Let("ciccio", My_dict(DictEl(("a", Ebool false), DictEl(("b", Ebool true), Empty))), 
              ApplyOver(Den "funzione", Den "ciccio"))), 
      []);;

eval( Let("funzione", Fun("x", Sum(Den "x", Eint 5)),
          Let("ciccio", My_dict(DictEl(("a", Eint 15), DictEl(("b", Eint 20), Empty))), 
              ApplyOver(Den "funzione", Den "ciccio"))), 
      []);;

eval( Let("funzione", Fun("x", Con(Den "x", Estring " tuo")),
          Let("ciccio", My_dict(DictEl(("a", Estring "cane"), DictEl(("b", Estring "gatto"), Empty))), 
              ApplyOver(Den "funzione", Den "ciccio"))), 
      []);



