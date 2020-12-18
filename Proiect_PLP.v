Require Import Strings.String.
Delimit Scope string_scope with string.
Local Open Scope string_scope.
Require Import Coq.Strings.Byte.
Local Open Scope list_scope.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
Set Implicit Arguments.
Open Scope list_scope.
Scheme Equality for string.


Inductive ErrNat :=
  | err_nat : ErrNat
  | num : nat -> ErrNat.

Inductive ErrBool :=
  | err_bool : ErrBool
  | boolean : bool -> ErrBool.

Inductive ErrString :=
  | err_string : ErrString
  | str : string -> ErrString.

Inductive ErrPointer :=
 | err_pointer : ErrPointer
 | NULL : ErrPointer
 | pointer : string -> ErrPointer
 | reference : string -> ErrPointer .

Scheme Equality for ErrPointer.

Coercion num: nat >-> ErrNat.
Coercion boolean: bool >-> ErrBool.
Coercion str: string >-> ErrString.



Check 7.
Check false.
Check "x".

(*Arithmetic expressions *)

Inductive AExp :=
| avar: string -> AExp 
| anum: ErrNat -> AExp
| aplus: AExp -> AExp -> AExp
| aminus: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp 
| adiv: AExp -> AExp -> AExp 
| amod: AExp -> AExp -> AExp
| ainc : AExp -> AExp
| adec : AExp -> AExp
| strlen : ErrString -> AExp.


Coercion anum: ErrNat >-> AExp.
Coercion avar: string >-> AExp. 

(*Operations with arithmetic expressions *)

Definition plus_err (a b : ErrNat) : ErrNat :=
 match a,b with 
 | err_nat, _ => err_nat
 | _, err_nat => err_nat
 | num a, num b => num (a + b)
end.

Definition minus_err (a b : ErrNat) : ErrNat :=
 match a,b with 
 | err_nat, _ => err_nat
 | _, err_nat => err_nat
 | num a, num b => if (ltb a b)
                   then err_nat
                   else num (a - b)
end.

Definition mul_err (a b : ErrNat) : ErrNat :=
 match a,b with 
 | err_nat, _ => err_nat
 | _, err_nat => err_nat
 | num a, num b => num (a * b)
end.

Definition div_err (a b : ErrNat) : ErrNat :=
 match a,b with 
 | err_nat, _ => err_nat
 | _, err_nat => err_nat
 | _, num 0 => err_nat
 | num a, num b => num (div a b)
end.


Definition mod_err (a b : ErrNat) : ErrNat :=
 match a,b with 
 | err_nat, _ => err_nat
 | _, err_nat => err_nat
 | _, num 0 => err_nat
 | num a, num b => num  (modulo a b)
end.

Definition inc (a : ErrNat) : ErrNat :=
 match a with
  | err_nat => err_nat
  | num a => num (a + 1)
 end.

Definition dec (a : ErrNat) : ErrNat :=
 match a with
  | err_nat => err_nat
  | 0 => err_nat
  | num a => num (a - 1)
 end.

(*Boolean expressions *)

Inductive BExp :=
| b_err : ErrString -> BExp
| b_true : BExp
| b_false : BExp
| b_var: string -> BExp 
| b_less : AExp -> AExp -> BExp
| b_more : AExp -> AExp -> BExp
| b_less_eq : AExp -> AExp -> BExp
| b_more_eq : AExp -> AExp -> BExp
| b_equal : AExp -> AExp -> BExp
| b_not : BExp -> BExp
| b_and : BExp -> BExp -> BExp
| b_or : BExp -> BExp -> BExp
| b_xor : BExp -> BExp -> BExp.

Coercion b_var : string >-> BExp.
Coercion b_err : ErrString >-> BExp.


(*Operations with boolean expressions*)

Definition less_err (b1 b2 : ErrNat) : ErrBool :=
  match b1, b2 with
    | err_nat, _ => err_bool
    | _, err_nat => err_bool
    | num x, num y => boolean (Nat.ltb x y)
    end.

Definition more_err (b1 b2 : ErrNat) : ErrBool :=
  match b1, b2 with
    | err_nat, _ => err_bool
    | _, err_nat => err_bool
    | num x, num y => boolean (negb (Nat.ltb x y)) 
    end.

Definition less_eq_err (b1 b2 : ErrNat) : ErrBool :=
 match b1, b2 with
  | err_nat, _ => err_bool
  | _, err_nat => err_bool
  | num x, num y => boolean (Nat.leb x y)
 end.

Definition more_eq_err (b1 b2 : ErrNat) : ErrBool :=
 match b1, b2 with
  | err_nat, _ => err_bool
  | _, err_nat => err_bool
  | num x, num y => boolean (negb (Nat.leb x y))
 end.

Definition equal_err (b1 b2 : ErrNat) : ErrBool :=
 match b1, b2 with
  | err_nat, _ => err_bool
  | _, err_nat => err_bool
  | num x, num y => boolean (Nat.eqb x y)
 end.

Definition not_err (n : ErrBool) : ErrBool :=
  match n with
    | err_bool => err_bool
    | boolean m => boolean (negb m)
    end.

Definition and_err (b1 b2 : ErrBool) : ErrBool :=
  match b1, b2 with
    | err_bool, _ => err_bool
    | _, err_bool => err_bool
    | boolean x, boolean y => boolean (andb x y)
    end.

Definition or_err (b1 b2 : ErrBool) : ErrBool :=
  match b1, b2 with
    | err_bool, _ => err_bool
    | _, err_bool => err_bool
    | boolean x, boolean y => boolean (orb x y)
    end.


Definition xorb_err (b1 b2 : ErrBool) : ErrBool :=
  match b1, b2 with
    | err_bool,_ => err_bool
    | _, err_bool => err_bool
    | true, true => false
    | true, false => true
    | false, true => true
    | false, false => false
  end.

(*String expressions *)

Inductive STRexp :=
 | str_err : ErrString -> STRexp
 | str_var : string -> STRexp
 | strcmp : ErrString -> ErrString -> STRexp
 | strcat : ErrString -> ErrString -> STRexp.

Coercion str_var : string >-> STRexp.
Coercion str_err : ErrString >-> STRexp.

(*Operations with strings *)

Definition str_length (s : ErrString) : ErrNat :=
 match s with 
  | err_string => err_nat
  | str s1 => length s1
 end.



Definition str_cat (s1 s2 : ErrString) : ErrString :=
 match s1,s2 with
  | err_string, _ => err_string
  | _, err_string => err_string
  | str s1, str s2 => str (s1 ++ s2)
 end.

Definition str_cmp (s1 s2 : ErrString) : ErrString :=
 match s1,s2 with 
  | err_string, _ => err_string
  | _, err_string => err_string
  | str s1, str s2 =>
     if (ltb (length s1) (length s2))
     then s2
     else s1
 end.


(*Arrays*)



Inductive ErrArray :=
 | err_array : ErrArray
 | array_n : string -> nat -> (list nat) -> ErrArray
 | array_b : string -> nat -> (list bool) -> ErrArray
 | array_s : string -> nat -> (list string) -> ErrArray.
 


(* Array operations *)

Inductive Array_opp :=
 | arr_len : ErrArray -> Array_opp
 | elem : string -> nat -> Array_opp
 | delete : string -> nat -> Array_opp
 | min : ErrArray -> Array_opp
 | max : ErrArray -> Array_opp.



(*Statements*)

Inductive Statement :=
  | nat_decl: string -> AExp -> Statement 
  | bool_decl: string -> BExp -> Statement 
  | str_decl : string -> STRexp -> Statement
  | array_decl_n : string -> nat -> (list nat) -> Statement
  | array_decl_b : string -> nat  -> (list bool) -> Statement
  | array_decl_s : string -> nat -> (list string) -> Statement
  | ptr_nat_decl : string -> string -> Statement
  | ptr_bool_decl : string -> string -> Statement
  | ptr_string_decl : string -> string -> Statement
  | ref_decl : string -> string -> Statement
  | nat_assign : string -> AExp -> Statement 
  | bool_assign : string -> BExp -> Statement
  | str_assign : string -> string -> Statement
  | ptr_assign : string -> string -> Statement
  | ref_assign : string -> string -> Statement
  | array_assign_n : string -> nat -> (list nat) -> Statement
  | array_assign_b : string -> nat -> (list bool) -> Statement
  | array_assign_s : string -> nat -> (list string) -> Statement 
  | sequence : Statement  -> Statement  -> Statement 
  | cin : string -> Statement (*input -> variable *)
  | cout : STRexp -> Statement
  | while : BExp -> Statement -> Statement
  | for_new : Statement -> BExp -> Statement -> Statement
  | ifthen : BExp -> Statement -> Statement
  | ifthenelse : BExp -> Statement -> Statement -> Statement
  | break : Statement
  | continue : Statement
  | switchcase : AExp -> list Case -> Statement
  | fun_call : string -> (list string) -> Statement (*apel de functie cu o serie de parametrii *)
   with Case :=
    | case_default : Statement -> Case
    | case : AExp -> Statement -> Case.



Inductive Types :=
  | err_undecl : Types (*  Error - variable used undeclared *)
  | err_assign : Types (* Error - declared a type , assigned other *)
  | default : Types (* default value for a variable *)
  | val_nat : ErrNat -> Types (*valorile pe care le atribui unei variabile declarate  nat*)
  | val_bool : ErrBool -> Types (* -|| de tip bool *)
  | val_string : ErrString -> Types (* -||- de tip string *)
  | val_pointer : ErrPointer -> Types
  | val_array : ErrArray -> Types
  | code : Statement -> Types. (* function code  *)

Coercion code : Statement >-> Types.


(*Inductive type for functions *)

Inductive Pgm :=
| secv : Pgm -> Pgm -> Pgm (*Secventa de funcii si/sau declaratii de variabile *)
| default_nat_decl : string -> Pgm (*declarare nat cu valoare default*)
| default_bool_decl : string -> Pgm (*declarare int cu valoare default*)
| default_string_decl : string -> Pgm (*declarare string cu valoare default*)
| default_array_decl : string -> nat -> Pgm
| default_ptr_decl : string -> Pgm
| main : Statement -> Pgm (* main function - no parameters *)
| function : string -> list string -> Statement -> Pgm. (* functions *)



(* Default values types - used for variables of different types outside a function *)

(*---> SEMANTICA*)


Definition type_equality  (t1 : Types)(t2 : Types) : bool :=
 match t1 with 
 | err_undecl => match t2 with 
                 | err_undecl => true
                 | _ => false
                end
 | err_assign => match t2 with 
                 | err_assign => true
                 | _ => false
                end
 | default => match t2 with 
                 | default => true
                 | _ => false
                end
 | val_nat a => match t2 with
              | val_nat b => true
              | _ => false
              end
 | val_bool b1 => match t2 with
              | val_bool b2 => true
              | _ => false
              end
 | val_string s1 => match t2 with
              | val_string s2 => true
              | _ => false
              end
 | val_pointer p1 => match t2 with
                    | val_pointer p2 => true
                    | _ => false
                     end
 | val_array v1 => match t2 with
                   | val_array v2 => true
                   | _ => false
                   end
 | code _x => match t2 with
                  | code _x => true
                  | _ => false
                 end
  end.

Compute (type_equality err_undecl err_assign ).
Compute (type_equality (val_nat 100) (val_bool false)).
Compute (type_equality (val_string "s1") (val_string "s2")).

(*Configuration for functions : <Env, Memory, Stack> *)

Inductive Memory :=
  | default_mem : Memory
  | offset : nat -> Memory.

Scheme Equality for Memory.

Definition Env := string -> Memory. (* mapare nume_varialiba -> zona de memorie*)

Definition MemLayer := Memory -> Types. (*mapare zona_memorie -> un tip anume indicat *)

Definition Stack := list Env. (*lista de env-uri ce se actualizeaza pe parcursul rularii programului*)

Inductive Config :=
  | config : nat -> Env -> MemLayer -> Stack -> Config.
 (* current memory zone -> environment -> memory layer -> stack *)

Definition update_env (env : Env) (v : string) (m : Memory) : Env :=
  fun y =>
      if (andb (string_beq v y ) (Memory_beq (env y) default_mem))
      then
        m
      else
        (env y).
Notation "S [ V // X ]" := (update_env S X V) (at level 0).

(*Daca variabila nu are nici macar default_mem  , returnam env 
 Daca variabila are default_mem / altceva , actualizam cu noul offset la care se afla variabila *)


Definition env : Env := fun x => default_mem. (*env initial *)
Compute (env "var"). (*"var" nu are asignata inca o zona de memorie *)
Compute (update_env env "var" (offset 5)) "var". (*ii schimbam variabilei "var" offset-ul la 5*)

Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Memory) (v : Types) : MemLayer :=
  fun y => 
      if(andb (Memory_beq (env x) type) (Memory_beq y type))
      then
        if(andb(type_equality err_undecl (mem y)) (negb(type_equality default v)))
        then err_undecl
        else if (type_equality err_undecl (mem y))
            then default
            else if(orb(type_equality default (mem y)) (type_equality v (mem y)))
                 then v
                 else err_assign
      else (mem y).

Notation "S [ V /m/ X ]" := (update_mem S X V) (at level 0).

Definition mem : MemLayer := fun x => err_undecl.


(*Notations & examples for arithmetic expressions *)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (aminus A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "A +++" := (ainc A) (at level 40,left associativity).
Notation "A ---" := (adec A) (at level 49). 

Check (2 +' 3 *' 5).
Check (2 +' 3 *' "n").
Check ("sum" /' "sum"---).
Check ("i" +++).
Check (3 %' 0).

(*Notations & examples for boolean expressions *)
Notation "A <' B" := (b_less A B) (at level 53).
Notation "A >' B" := (b_more A B) (at level 53).
Notation "A <=' B" := (b_less_eq A B) (at level 53).
Notation "A >=' B" := (b_more_eq A B) (at level 53).
Notation "A == B" := (b_equal A B) (at level 53).
Notation " ! A " := (b_not A) (at level 71).
Notation "A & B" := (b_and A B) (at level 75).
Notation "A | B" := (b_or A B) (at level 75).
Notation "A ^^ B" := (b_xor A B) (at level 60).

Check ( 3 >=' ("x" /' 0)) .
Check (( ("a" +' 5) /' (("b" -'1) *' 3)) <=' 100 ).
Check (( ! b_false ) & b_true).
Check ( b_true | b_false | "sum" | ("a" <=' "b")).
Check (b_true ^^ b_false).
Check ("a" ^^ "b").


(*Notations & examples for string operations *)
Notation " len[ S ] " := (strlen S) (at level 31).
Notation " S1 /+/ S2 " := (strcat S1 S2) (at level 30).
Notation " S1 ? S2 " := (strcmp S1 S2) (at level 32).


Check ("Info " /+/ "PLP") .
Check (len[ "Proiect" ]).
Check ("ab" ? "ba") .


(*Notations & examples for arrays*)
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.


Check  [1 , 3 , 5 , 8].
Check [].
Check [true , false].
Check ["proiect" , "PLP"].

Notation "'Nat_array' A '[(' X ')]' -> L " :=(array_decl_n A X L)(at level 4).
Notation " A '[[' X ']]' n->  L  " := (array_assign_n A X L) (at level 30).

Notation "'Bool_array' B '[(' X ')]' -> L " :=(array_decl_b B X L)(at level 4).
Notation " B '[[' X ']]' b->  L  " := (array_assign_b B X L) (at level 30).


Notation "'Str_array' S '[(' X ')]' -> L " :=(array_decl_s S X L)(at level 4).
Notation " S '[[' X ']]' s->  L  " := (array_assign_s S X L) (at level 30).

Notation " s [[' i ']] " := (elem s i)(at level 22).


Check Nat_array "x"[(2)] -> [100 , 100].
Check Bool_array "booleans"[(3)] -> [false, false, false].
Check Str_array "homework"[(2)] -> ["PLP","Part1"].

Check "x"[[2]] n-> [ 0, 1].
Check "booleans"[[3]] b-> [true,true,false].
Check "homework"[[2]] s-> ["project", "syntax"].

Check "x"[['2']].


(*Notations & examples for statements & functions *)

Notation " A **" := (pointer A)(at level 30).
Notation "&& A" := (reference A )(at level 30).

Notation "'NAT' X ::= A  " := (nat_decl X A)(at level 90).
Notation "'BOOL' X ::= A " := (bool_decl X A)(at level 90).
Notation "'STR' X ::= A " := (str_decl X A) (at level 90).



Notation " X := 'NAT**' A " := (ptr_nat_decl X A) (at level 90).
Notation " X := 'BOOL**' A " := (ptr_bool_decl X A) (at level 90).
Notation " X := 'STR**' A " := (ptr_string_decl X A) (at level 90).
Notation " X := '&&' A " := (ref_decl X A) (at level 90).



Notation "'Default_nat' X" := (default_nat_decl X) (at level 90).
Notation "'Default_bool' B" := (default_bool_decl  B) (at level 90).
Notation "'Default_str' S" := (default_string_decl S) (at level 90).
Notation "'Default_arr' A '[(' X ')]'" := (default_array_decl A X) (at level 90).
Notation "'Default_ptr' P" := (default_ptr_decl P) (at level 90).

Notation "X n:= A" := (nat_assign X A)(at level 80).
Notation "X b:= A" := (bool_assign X A)(at level 90).
Notation "X s:= A" := (str_assign X A)(at level 90).
Notation "X p:= '**' A" := (ptr_assign X A)(at level 90).
Notation "X r:= '&&' A" := (ref_assign X A)(at level 90).


Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "S1 ;.; S2" := (secv S1 S2) (at level 93, right associativity).

Notation " 'While' '(' B ')' '{' S '}' 'End' " := (while B S) (at level 97).
Notation "'For' ( A ~ B ~ C ) 'Do' { S } 'End'" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'If' '(' B ')' 'Then' '(' S1 ')' 'Else' '(' S2 ')' 'End'" := (ifthenelse B S1 S2) (at level 97).
Notation "'If'(' B ) 'Then'{' S '}End'" := (ifthen B S) (at level 97).

Notation "'default:{' S };" := (case_default S) (at level 97).
Notation "'case(' X ):{ S };" := (case X S) (at level 97).
Notation "'SWITCH' '(' Y ){ case_1 .. case_n '}'" := (switchcase Y (cons case_1 .. (cons case_n nil) .. )) (at level 40).

Notation "'int' 'main()' { S }" := (main S)(at level 90). 
Notation "'int' F (){ S }" := (function F nil S)(at level 90).
Notation "'int' F (( p_1 , .. , p_n )){ S }" := (function F (cons p_1 .. (cons p_n nil) .. ) S)(at level 90).


Notation "'cin>>(' I )" := (cin I) (at level 92).
Notation "'cout<<(' O )" := (cout O) (at level 92).

Notation "'f_call' F (( p_1 , .. , p_n ))" := (fun_call F (cons p_1 .. (cons p_n nil) .. ) ) (at level 89).
Notation "'f_call' F (( ))" := (fun_call F nil) (at level 89).


Check Default_nat "i".
Check NAT "x" ::= 0.
Check BOOL "y" ::= b_true.
Check STR "s" ::= "sum".

Check "ptr" **.
Check &&"var".



Check 
   "a" n:= 27 ;;  "b" n:= 3 ;;  "r" n:= 0 ;;
  While
      ( "b" )
      {"r" n:= "a" %' "b" ;;
       "a" n:= "b" ;;
       "b" n:= "r" } End.

Check
    (NAT "sum" ::= 0) ;;
    (BOOL "k" ::= b_true) ;;
       For ( NAT "i" ::= 0 ~ "i" <=' (length("var") *' 3) ~ "i" n:= "i" +++ )
         Do {
           "sum" n:= "sum" +' "i" ;;
            "k" b:= b_false
            } End.

Check
 (NAT "value" ::= 10) ;; 
 (NAT "min" ::= 0 ) ;;
 (NAT "max" ::= 100) ;;
 If ( "max" <=' "value" )
   Then ( "max" b:= "value" )
   Else ( "min" b:= "value" )
End.

Check
 (STR "sir1" ::= "PLP") ;;
 (STR "sir2" ::= "Project") ;;
  If'( (length("sir1") ) >' (length("sir2") ) ) 
  Then'{
       STR "rez" ::= ("sir1")
     }End.


Check SWITCH( 0 ){ default:{ "a" n:= 0 };}.




Check

  Default_nat "i" ;.;
  Default_bool "k" ;.;
  int "printf" (("result")){
   cout<<("result")
} ;.;

  int main(){
    (NAT "max" ::= 0) ;; (NAT "min" ::=100) ;;
    (NAT "contor" ::= 50) ;;
    (NAT "n" ::= 1) ;;
    If'("k") Then'{
        "n" s:= "k"
     }End ;;
     While
      ( ! ("k") )
      { If ( "max" <=' "contor" )
            Then ( "max" b:= "contor" ;; break )
            Else ( "min" b:= "contor" )End 
      } End ;;
    f_call "printf"(( "max" )) ;;
    f_call "printf"(( "min" ))
  }.

Check Default_ptr "NULL".
Check  "a" := && "b".

Check ( "nat_pointer" := NAT** "n") ;; ( "n" p:= ** "p")  .
Check ( "bool_pointer" := BOOL** "bool") ;; ( "bool" r:= && "b_true").
Check  ( "string_pointer" := STR** "str")  ;; ("str" r:= && "syntax").

Check (BOOL "new" ::= b_false) ;;
      ( "new" p:=** "ok" ) ;; ("ok" r:= && "new").


























