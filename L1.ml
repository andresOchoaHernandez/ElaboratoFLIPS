(* ============================== FIBONACCI ============================== *)
(*
    fibonacci (n) :

      if n == 0:
        return 0
      else
          if n == 1:
            return 1
          els
            return fibonacci(n-1) + fibonacci(n-2)

La funzione viene applicata con argomento n, controlla se è uguale a 0, se lo è ritorna 0 altrimenti controlla
se n è uguale a 1, se lo è ritorna 1 altrimenti chiama in modo ricorsivo se stessa con argomento n-1 e lo sommerà al risultato dell'altra chiamata
ricorsiva che avrà come argomento n-2

printred(CBNapp(CBNfix (CBNfn(funtype(int,int),CBNfn(int,If(Op(Var 0, uguale, Integer 0),Integer 0,If(Op(Var 0,uguale,Integer 1),Integer 1,Op(CBNapp(Var 1,Op(Var 0, meno,Integer 1)),piu,CBNapp(Var 1,Op(Var 0, meno,Integer 2)))))))),Integer 13),[]);

Che calcola il 13esimo elemento della sequenza di fibonacci, ossia 233 -->  < 233 , {} >
*)

load "Listsort";
load "Int";
load "Bool";

(* ========================================= SINTASSI ========================================= *)
datatype type_L =  int  | unit  | bool | funtype of type_L * type_L; 

datatype oper = piu | meno | uguale | mu;

datatype type_loc = intref

type loc = string

type store = (loc * int) list

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
  |   Var of int 
  |   CBNfn of type_L * exp   
  |   CBNapp of exp * exp     
  |   CBNfix of exp           

(* ################ FUNZIONI DI SUPPORTO ################ *)

(* Controlla se ho un valore o un'espressione *)
fun is_val (Integer n)  = true
|   is_val (Boolean b)  = true
|   is_val (Skip)       = true
|   is_val (CBNfn(t,e)) = true  
|   is_val _ = false

(* Ritorna il valore di una locazione nello store *)
fun lookup ( [], l ) = NONE
  | lookup ( (l',n')::pairs, l) = 
    if l=l' then SOME n' else lookup (pairs,l)

(* Ritorna un elemento ad una data posizione *)
fun takeElementAt [] m = NONE
| takeElementAt (hd::tl) m = if m=0 then SOME hd else takeElementAt tl (m-1)

(* Aggiorna/aggiunge una coppia (loc,val) allo store e ritorna quello aggiornato appongiandosi ad una funzione di supporto *)
fun update'  front [] (l,n) = NONE
 |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
        SOME(front @ ((l,n)::pairs) )
    else 
        update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n)

(* Sostituzione *)
fun substitute expression x (Integer n)         = Integer n
|   substitute expression x (Boolean b)         = Boolean b
|   substitute expression x (Skip)              = Skip
|   substitute expression x (Op(e1,operand,e2)) = Op( substitute expression x e1, operand, substitute expression x e2 )
|   substitute expression x (If(e1,e2,e3))      = If( substitute expression x e1, substitute expression x e2, substitute expression x e3 )
|   substitute expression x (Assign(l,e1))      = Assign( l,substitute expression x e1 )
|   substitute expression x (Deref l)           = Deref l
|   substitute expression x (Var v)             = if x = v then expression else Var v
|   substitute expression x (Seq(e1,e2))        = Seq( substitute expression x e1, substitute expression x e2 )
|   substitute expression x (While(e1,e2))      = While( substitute expression x e1, substitute expression x e2 )
|   substitute expression x (CBNfn(t,e))        = CBNfn( t,substitute expression (x+1) e )
|   substitute expression x (CBNapp(e1,e2))     = CBNapp( substitute expression x e1,substitute expression x e2 )
|   substitute expression x (CBNfix e)          = CBNfix( substitute expression x e )

(* ###################################################### *)

(* =================================== SEMANTICA SMALL STEP =================================== *)

(* Implementa le regole di riduzione di L1 per tutti i costrutti specificati nella sintassi *)
fun reduction (Integer n,s) = NONE                                                (* Integer caso base *)
|   reduction (Boolean b,s) = NONE                                                (* Boolean caso base *)
|   reduction (Skip,s)      = NONE                                                                      
|   reduction (Op (e1,opr,e2),s) =                                                (*Operation*)                                  
        (case (e1,opr,e2) of                                                      (*|         *)                       
          (Integer x1, piu, Integer x2)    => SOME(Integer (x1+x2), s)            (*|--[  + ] *)                
        | (Integer x1, meno, Integer x2)   => SOME(Integer (x1-x2), s)            (*|--[  - ] *)      
        | (Integer x1, uguale, Integer x2) => SOME(Boolean (x1=x2), s)            (*|--[ == ] *)                      
        | (Integer x1, mu, Integer x2)     => SOME(Boolean (x1 >= x2), s)         (*|--[ >= ] *)                                    
        | (e1,opr,e2) => (                                                                                                
            if (is_val e1) then (                                                 (* op2 *)                                   
                case reduction (e2,s) of                                                                                      
                    SOME (e2',s') => SOME (Op(e1,opr,e2'),s')                                                             
                | NONE => NONE )                                                                                      
            else (                                                                (* op1 *)                                  
                case reduction (e1,s) of                                                                            
                    SOME (e1',s') => SOME(Op(e1',opr,e2),s')                                                                  
                | NONE => NONE ) ) )                                                                          
|   reduction (If (e1,e2,e3),s) =                                                 (* If *)              
        (case e1 of                                                                                       
            Boolean(true) => SOME(e2,s)                                                                             
        | Boolean(false) => SOME(e3,s)                                                                                
        | _ => (case reduction (e1,s) of                                                                            
                    SOME(e1',s') => SOME(If(e1',e2,e3),s')                                                        
                    | NONE => NONE ))                                                                       
|   reduction (Deref l,s) =                                                       (* Deref *)                                
        (case lookup  (s,l) of                                                                                          
            SOME n => SOME(Integer n,s)                                                                                       
            | NONE => NONE )                                                                                      
|   reduction (Var v,s) = NONE                                                    (* Var *)                                      
|   reduction (Assign (l,e),s) =                                                  (* Assign *)                                        
        (case e of                                                                                                        
            Integer n => (case update (s,(l,n)) of                                                                        
                            SOME s' => SOME(Skip, s')                                                                     
                            | NONE => NONE)                                                                                 
        | _ => (case reduction (e,s) of                                                                                 
                    SOME (e',s') => SOME(Assign (l,e'), s')                                                             
                    | NONE => NONE  ) )                                                                                   
|   reduction (While (e1,e2),s) = SOME( If(e1,Seq(e2,While(e1,e2)),Skip),s)       (* While *)                                              
|   reduction (Seq (e1,e2),s) =                                                   (* Sequnce *)                                               
        (case e1 of                                                                                                   
            Skip => SOME(e2,s)                                                                                            
        | _ => ( case reduction (e1,s) of                                                                                 
                    SOME (e1',s') => SOME(Seq (e1',e2), s')                                                             
                | NONE => NONE ) )                                                                                  
|   reduction (CBNfn(t,e),s) = NONE                                                (* [CBN] function *)                                         
|   reduction (CBNapp(e1,e2),s) =                                                  (* [CBN] apply function *)                   
      (case e1 of                                                                                                         
        CBNfn(t,e) => SOME(substitute e2 0 e,s) |                                                                          
        _          => (                                                                                                   
          case reduction(e1,s) of                                                                                         
            SOME(e1',s') => SOME(CBNapp(e1',e2),s') |                                                                        
            _            => NONE ))                                                                                         
|   reduction (CBNfix(e),s) = SOME(CBNapp(e,CBNfix(e)),s)                           (* [CBN] fix *)                                        

(* =================================== SEMANTICA BIG STEP   =================================== *)

fun evaluate (e,s) = case reduction (e,s) of 
                         NONE => (e,s)
                       | SOME (e',s') => evaluate (e',s')

(* =================================== TIPAGGIO ================================================ *)
fun infertype gamma (Integer n) = SOME int
|   infertype gamma (Boolean b) = SOME bool
|   infertype gamma (Op (e1,oper,e2)) 
      = (case (infertype gamma e1, oper, infertype gamma e2) of
           (SOME int, piu,    SOME int) => SOME int
          |(SOME int, meno,   SOME int) => SOME int
          |(SOME int, uguale, SOME int) => SOME bool
          |(SOME int, mu,     SOME int) => SOME bool 
          |_ => NONE)
|   infertype gamma (If (e1,e2,e3)) 
      = (case (infertype gamma e1, infertype gamma e2, infertype gamma e3) of
          (SOME bool, SOME type_e2, SOME type_e3) => 
          (if type_e2=type_e3 then SOME type_e2 else NONE)
          |_ => NONE)
|   infertype gamma (Deref l) 
      = (case lookup ((#1 gamma),l) of
          SOME intref => SOME int
          | NONE => NONE)
|   infertype gamma (Assign (l,e)) 
      = (case (lookup ((#1 gamma),l), infertype gamma e) of
        (SOME intref,SOME int) => SOME unit
        | _ => NONE)
|   infertype gamma (Skip) = SOME unit
|   infertype gamma (Var n) = takeElementAt (#2 gamma) n
|   infertype gamma (Seq (e1,e2))  
      = (case (infertype gamma e1, infertype gamma e2) of
        (SOME unit, SOME t2) => SOME t2
        | _ => NONE )
|   infertype gamma (While (e1,e2)) = (case (infertype gamma e1, infertype gamma e2) of (SOME bool, SOME unit) => SOME unit | _ => NONE )
|   infertype gamma (CBNfn (t,e))   = (case (infertype (#1 gamma, t::(#2 gamma)) e) of (SOME t1 ) => SOME (funtype (t,t1)) | _ => NONE) 
|   infertype gamma (CBNapp (f,x))  = (case (infertype gamma f, infertype gamma x) of (SOME (funtype (t1, t2)), SOME ta) => (if t1 = ta then SOME t2 else NONE) | _ => NONE)
|   infertype gamma (CBNfix e) = (case (infertype gamma e) of SOME (funtype(funtype (t1, t2), (funtype(t1', t2')))) => (if t1 = t1' andalso t2 = t2' then SOME (funtype (t1, t2)) else NONE) | _ => NONE);

(* =================================== FUNZIONI PER STAMPARE =================================== *)

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
  | printexp (CBNfn (t,e)) = "CBNfn " ^ printexp(e)
  | printexp (CBNapp(e1,e2)) = "CBNapp(" ^ (printexp(e1)) ^ ", " ^ (printexp(e2)) ^ ")" 
  | printexp (CBNfix(e)) = "CBNfix(" ^ (printexp(e)) ^ ")"
  | printexp (Var v) = "Var " ^ Int.toString(v)

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