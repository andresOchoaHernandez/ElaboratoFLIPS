(* ========================================= SINTASSI ========================================= *)

type loc = string

datatype oper = piu | meno | uguale | mu

datatype type_L =  int  | unit  | bool | function of type_L * type_L (* <========== FUNZIONI =======> *)

datatype type_loc = intref

type typeE = (loc*type_loc) list

datatype exp =
        Boolean of bool
    |   Integer of int
    |   Op of exp * oper * exp
    |   If of exp * exp * exp
    |   Assign of loc * exp
    |   Skip 
    |   Seq of exp * exp
    |   While of exp * exp
    |   Deref of loc
    |   CBNfn of type_L * exp   (* <========== FUNZIONI =======> *)
    |   CBNapp of exp * exp     (* <========== FUNZIONI =======> *)
    |   CBNfix of exp           (* <========== FUNZIONI =======> *)

type store = (loc * int) list

(* ################ FUNZIONI DI SUPPORTO ################ *)

(* Controlla se ho un valore o un'espressione *)
fun is_val (Integer n)  = true
|   is_val (Boolean b)  = true
|   is_val (Skip)       = true
|   is_val (CBNfn(t,e)) = true  (* <========== FUNZIONI =======> *)
|   is_val _ = false

(* Ritorna il valore di una locazione nello store *)
fun lookup ( [], l ) = NONE
  | lookup ( (l',n')::pairs, l) = 
    if l=l' then SOME n' else lookup (pairs,l)

(* Aggiorna/aggiunge una coppia (loc,val) allo store e ritorna quello aggiornato appongiandosi ad una funzione di supporto *)
fun update'  front [] (l,n) = NONE
 |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
        SOME(front @ ((l,n)::pairs) )
    else 
        update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n)

(* ###################################################### *)

(* =================================== SEMANTICA SMALL STEP =================================== *)

(* Implementa le regole di riduzione di L1 per tutti i costrutti specificati nella sintassi *)
fun reduction (Integer n,s) = NONE
|   reduction (Boolean b,s) = NONE
|   reduction (Skip,s)      = NONE  
|   reduction (Op (e1,opr,e2),s) = 
        (case (e1,opr,e2) of
          (Integer x1, piu, Integer x2)    => SOME(Integer (x1+x2), s)
        | (Integer x1, meno, Integer x2)   => SOME(Integer (x1-x2), s)
        | (Integer x1, uguale, Integer x2) => SOME(Boolean (x1=x2), s)
        | (Integer x1, mu, Integer x2)     => SOME(Boolean (x1 >= x2), s)
        | (e1,opr,e2) => (                                               
            if (is_val e1) then (                                        
                case reduction (e2,s) of 
                    SOME (e2',s') => SOME (Op(e1,opr,e2'),s')     
                | NONE => NONE )                           
            else (                                                 
                case reduction (e1,s) of 
                    SOME (e1',s') => SOME(Op(e1',opr,e2),s')      
                | NONE => NONE ) ) )
|   reduction (If (e1,e2,e3),s) =
        (case e1 of
            Boolean(true) => SOME(e2,s)                           
        | Boolean(false) => SOME(e3,s)                          
        | _ => (case reduction (e1,s) of
                    SOME(e1',s') => SOME(If(e1',e2,e3),s')      
                    | NONE => NONE ))
|   reduction (Deref l,s) = 
        (case lookup  (s,l) of                
            SOME n => SOME(Integer n,s)                          
            | NONE => NONE )                  
|   reduction (Assign (l,e),s) =                                  
        (case e of                                                 
            Integer n => (case update (s,(l,n)) of 
                            SOME s' => SOME(Skip, s')           
                            | NONE => NONE)                                   
        | _ => (case reduction (e,s) of                           
                    SOME (e',s') => SOME(Assign (l,e'), s')    
                    | NONE => NONE  ) )                          
|   reduction (While (e1,e2),s) = SOME( If(e1,Seq(e2,While(e1,e2)),Skip),s)                                   
|   reduction (Seq (e1,e2),s) =                                   
        (case e1 of                                                 
            Skip => SOME(e2,s)                                     
        | _ => ( case reduction (e1,s) of                           
                    SOME (e1',s') => SOME(Seq (e1',e2), s')       
                | NONE => NONE ) )
|   reduction (CBNfn(t,e),s) = NONE                         (* <========== FUNZIONI =======> *)
|   reduction (CBNapp(e1,e2),s) =                           (* <========== FUNZIONI =======> *)
      (case e1 of                                           (* <========== FUNZIONI =======> *)
        CBNfn(t,e) => SOME((* TODO replacement *)) |        (* <========== FUNZIONI =======> *) 
        _          => (                                     (* <========== FUNZIONI =======> *)
          case reduction(e1,s) of                           (* <========== FUNZIONI =======> *)
            SOME(e1',s') => SOME(CBNapp(e1',e2),s') |       (* <========== FUNZIONI =======> *)   
            _            => NONE ))                         (* <========== FUNZIONI =======> *)  
|   reduction (CBNfix(e),s) = SOME(CBNapp(e,CBNfix(e)),s)   (* <========== FUNZIONI =======> *)

(* =================================== SEMANTICA BIG STEP   =================================== *)

fun evaluate (e,s) = case reduction (e,s) of 
                         NONE => (e,s)
                       | SOME (e',s') => evaluate (e',s')

(* =================================== TIPAGGIO ================================================ *) 

fun infertype gamma (Integer n) = SOME int
  | infertype gamma (Boolean b) = SOME bool
  | infertype gamma (Op (e1,opr,e2)) 
    = (case (infertype gamma e1, opr, infertype gamma e2) of
          (SOME int, piu, SOME int) => SOME int
        | (SOME int, meno, SOME int) => SOME int
        | (SOME int, uguale, SOME int) => SOME bool
        | (SOME int, mu, SOME int) => SOME bool
        | _ => NONE)
  | infertype gamma (If (e1,e2,e3)) 
    = (case (infertype gamma e1, infertype gamma e2, infertype gamma e3) of
           (SOME bool, SOME t2, SOME t3) => 
           (if t2=t3 then SOME t2 else NONE)
         | _ => NONE)
  | infertype gamma (Deref l) 
    = (case lookup (gamma,l) of
           SOME intref => SOME int
         | NONE => NONE)
  | infertype gamma (Assign (l,e)) 
    = (case (lookup (gamma,l), infertype gamma e) of
           (SOME intref,SOME int) => SOME unit
         | _ => NONE)
  | infertype gamma (Skip) = SOME unit
  | infertype gamma (Seq (e1,e2))  
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME unit, SOME t2) => SOME t2
         | _ => NONE )
  | infertype gamma (While (e1,e2)) 
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME bool, SOME unit) => SOME unit 
         | _ => NONE );

(* =================================== FUNZIONI PER STAMPARE =================================== *)

load "Listsort";
load "Int";
load "Bool";

fun printop piu    = "+"
  | printop meno   = "-"
  | printop uguale = "=="
  | printop mu     = ">="
                         
fun printexp (Integer n) = Int.toString n
  | printexp (Boolean b) = Bool.toString b
  | printexp (Op (e1,opr,e2)) 
    = "(" ^ (printexp e1) ^ (printop opr) 
      ^ (printexp e2) ^ ")"
  | printexp (If (e1,e2,e3)) 
    = "if " ^ (printexp e1 ) ^ " then " ^ (printexp e2)
      ^ " else " ^ (printexp e3)
  | printexp (Deref l) = "!" ^ l
  | printexp (Assign (l,e)) =  l ^ ":=" ^ (printexp e )
  | printexp (Skip) = "skip"
  | printexp (Seq (e1,e2)) =  (printexp e1 ) ^ ";" 
                                     ^ (printexp e2)
  | printexp (While (e1,e2)) =  "while " ^ (printexp e1 ) 
                                       ^ " do " ^ (printexp e2)

fun printstore' [] = ""
  | printstore' ((l,n)::pairs) = l ^ "=" ^ (Int.toString n) 
                                   ^ " " ^ (printstore' pairs)

fun printstore pairs = 
    let val pairs' = Listsort.sort 
                         (fn ((l,n),(l',n')) => String.compare (l,l'))
                         pairs
    in
        "{" ^ printstore' pairs' ^ "}" end

fun printconf (e,s) = "< " ^ (printexp e) 
                             ^ " , " ^ (printstore s) ^ " >"

fun printred' (e,s) = 
    case reduction (e,s) of 
        SOME (e',s') => 
        ( TextIO.print ("\n -->  " ^ printconf (e',s') ) ;
          printred' (e',s'))
      | NONE => (TextIO.print "\n -/->  " ; 
                 if is_val e then 
                     TextIO.print "(a value)\n" 
                 else 
                     TextIO.print "(stuck - not a value)" )

fun printred (e,s) = (TextIO.print ("      "^(printconf (e,s))) ;
                          printred' (e,s))

(* ============================== TEST ============================== *)
(* TEST "MENO"   *)
(* printred(Assign("c",Op(Integer 1,meno,Integer 1)),[]); *)

(* TEST "UGUALE" *)
(* printred(Assign("c",Op(Integer 1,uguale,Integer 1)),[]); *)