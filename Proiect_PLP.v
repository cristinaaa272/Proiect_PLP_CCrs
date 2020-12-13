Require Import Strings.String.
Delimit Scope string_scope with string.
Local Open Scope string_scope.
Require Import Coq.Strings.Byte.
Local Open Scope list_scope.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Nat.


Inductive ErrNat :=
  | err_nat : ErrNat
  | num : nat -> ErrNat.

Inductive ErrBool :=
  | err_bool : ErrBool
  | boolean : bool -> ErrBool.

Inductive ErrString :=
  | err_string : ErrString
  | str : string -> ErrString.




Coercion num: nat >-> ErrNat.
Coercion boolean: bool >-> ErrBool.
Coercion str: string >-> ErrString.


Check 7.
Check false.
Check "x".

Inductive AExp :=
| avar: string -> AExp (* Variabilele sunt acum stringuri *)
| anum: ErrNat -> AExp
| aplus: AExp -> AExp -> AExp
| aminus: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp 
| adiv: AExp -> AExp -> AExp 
| amod: AExp -> AExp -> AExp
| ainc : AExp -> AExp
| adec : AExp -> AExp.


Coercion anum: ErrNat >-> AExp.
Coercion avar: string >-> AExp. 

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

Inductive BExp :=
| b_err : BExp
| b_true : BExp
| b_false : BExp
| b_var: string -> BExp 
| b_lessthan : AExp -> AExp -> BExp
| b_morethan : AExp -> AExp -> BExp
| b_not : BExp -> BExp
| b_and : BExp -> BExp -> BExp
| b_or : BExp -> BExp -> BExp
| b_xor : BExp -> BExp -> BExp.

Coercion b_var : string >-> BExp.

Definition lessthan_err (b1 b2 : ErrNat) : ErrBool :=
  match b1, b2 with
    | err_nat, _ => err_bool
    | _, err_nat => err_bool
    | num x, num y => boolean (ltb x y)
    end.

Definition morethan_err (b1 b2 : ErrNat) : ErrBool :=
  match b1, b2 with
    | err_nat, _ => err_bool
    | _, err_nat => err_bool
    | num x, num y => boolean (negb (ltb x y)) 
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



(*Statements*)

Inductive Statement :=
  | nat_decl: string -> Statement 
  | bool_decl: string  -> Statement 
  | str_decl : string -> Statement
  | array_decl_n : string  -> Statement
  | array_decl_b : string  -> Statement
  | array_decl_s : string  -> Statement
  | nat_assign : string -> AExp -> Statement 
  | bool_assign : string -> BExp -> Statement
  | str_assign : string -> string -> Statement
  | array_assign_n : string -> (list nat) -> Statement
  | array_assign_b : string -> (list bool) -> Statement
  | array_assign_s : string -> (list string) -> Statement 
  | sequence : Statement  -> Statement  -> Statement 
  | while : BExp -> Statement -> Statement
  | for_new : Statement -> BExp -> Statement -> Statement
  | ifthen : BExp -> Statement -> Statement
  | ifthenelse : BExp -> Statement -> Statement -> Statement.

(*Arrays*)

Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.

Set Implicit Arguments.
Open Scope list_scope.

Inductive ErrArray :=
 | err_array : ErrArray
 | array_n : string -> (list nat) -> ErrArray
 | array_b : string -> (list bool) -> ErrArray
 | array_s : string -> (list string) -> ErrArray.
 

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.



Section Lists.
Check  [1 , 3 , 5 , 8].
Check [].
Check [true , false].
Check ["proiect" , "PLP"].

Notation "'Nat_array' A " :=(array_decl_n A)(at level 4).
Notation "'Bool_array' B " :=(array_decl_b B)(at level 4).
Notation "'Str_array' S " :=(array_decl_s S)(at level 4).


Notation " A n:=  X  " := (array_assign_n A X) (at level 30).
Notation " A b:=  B  " := (array_assign_b A B) (at level 30).
Notation " A s:=  S  " := (array_assign_s A S) (at level 30).


Check (Nat_array "x").
Check (Bool_array "booleans").
Check (Str_array "strs").

Check ("x" n:= [ 1 , 2 ]).
Check ("booleans" b:= [ false , true ]).
Check ("strs" s:= [ "project" , "syntax"]).

(* Array operations *)

Inductive Array_opp :=
 | insert : ErrArray -> Array_opp
 | delete : ErrArray -> Array_opp
 | find : ErrArray -> Array_opp.



(*String operations*)

Inductive Strings_opp :=
 | strlen : ErrString -> Strings_opp
 | strcmp : ErrString -> ErrString -> Strings_opp
 | strcat : ErrString -> ErrString -> Strings_opp.


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





(*Construim un TIP general de rezultat care inglobeaza mai multe tipuri pentru varialbile*)

Inductive Types :=
  | err_undecl : Types (* tip de eroare - variabila e folosita fara a fi declarata*)
  | err_assign : Types (* tip de eroare - atribui un bool desi am zis ca atribui nat*)
  | default_nat: Types (*o variabila nat , dupa declarare , primeste o valoare default*)
  | default_bool : Types
  | default_string : Types
  | val_nat : ErrNat -> Types (*valorile pe care le atribui unei variabile declarate  nat*)
  | val_bool : ErrBool -> Types (* -||- de tip bool *)
  | val_string : ErrString -> Types.



Scheme Equality for Types.
(*In momentul in care declari o variabila , ori ii dai o valoare default
ori o declari si o si initializezi cu o valoare *)

(* Env = mapare de la string-uri la tipul Types*)
Definition Env := string -> Types.

(* Env initial : orice variabila este undeclared ,pana o declar .
dupa ce o declar, primeste , dupa caz, valoarea default pentru nat/bool/string 
Abia dupa ce are o valoare default, ii putem asigna o alta valoare prin atribuire  *)
Definition env : Env := 
  fun x => err_undecl.
Compute (env "y").

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
 | default_nat => match t2 with 
                 | default_nat => true
                 | _ => false
                end
 | default_bool => match t2 with 
                 | default_bool => true
                 | _ => false
                end
 | default_string => match t2 with 
                 | default_string => true
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
  end.

Compute (type_equality err_undecl err_assign ).
Compute (type_equality (val_nat 100) (val_bool false)).
Compute (type_equality (val_string "s1") (val_string "s2")).



Definition update_env (env : Env) (x : string) (val : Types) : Env :=
 fun y =>
  if (string_beq y x) 
   then
     if(andb (type_equality err_undecl (env y)) (negb (type_equality default_nat val)))
       then err_undecl
       else 
           if (andb (type_equality err_undecl (env y)) (negb (type_equality default_bool val)))
           then err_undecl
           else 
              if(andb (type_equality err_undecl (env y)) (negb (type_equality default_string val)))
              then err_undecl
       else 
           if (andb (type_equality err_undecl (env y)) ((type_equality default_nat val)))
           then default_nat
           else 
             if (andb (type_equality err_undecl (env y)) ((type_equality default_bool val))) 
             then default_bool
             else
                if (andb (type_equality err_undecl (env y)) ((type_equality default_string val)))
                then default_string
        else 
           if(orb (type_equality default_nat (env y)) (type_equality val (env y)))
           then val
           else 
              if(orb (type_equality default_bool (env y)) (type_equality val (env y)))
              then val
              else
                 if(orb (type_equality default_string (env y)) (type_equality val (env y)))
                 then val
                 else err_assign

  else (env y).

Notation "E [ V // X ]" := (update_env E X V) (at level 0).

Compute (env "sum").

Compute (env [default_bool // "y"]).
Compute (update_env (update_env env "y" (default_nat)) "y" (val_bool true) "y").








  
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
Compute ("sum" /' "sum"---).
Compute ("i" +++).
Compute (3 %' 0).

(*Notations & examples for boolean expressions *)
Notation "A <=' B" := (b_lessthan A B) (at level 53).
Notation "A >=' B" := (b_morethan A B) (at level 53).
Notation " ! A " := (b_not A) (at level 71).
Notation "A & B" := (b_and A B) (at level 75).
Notation "A | B" := (b_or A B) (at level 75).
Notation "A ^^ B" := (b_xor A B) (at level 60).

Compute ( 3 >=' ("x" /' 0)) .
Compute (( ("a" +' 5) /' (("b" -'1) *' 3)) <=' 100 ).
Compute (( ! b_false ) & b_true).
Compute ( b_true | b_false | "sum" | ("a" <=' "b")).
Compute (b_true ^^ b_false).
Compute ("a" ^^ "b").

(*Notations & examples for string operations *)
Notation " len[ S ] " := (strlen S) (at level 31).
Notation " S1 /+/ S2 " := (strcat S1 S2) (at level 30).
Notation " S1 ? S2 " := (strcmp S1 S2) (at level 32).

Check ("Info " /+/ "PLP") .
Check (len[ "Proiect" ]).
Check ("ab" ? "ba") .

(*Notations & examples for statements*)
Notation "'NAT' X ::= A" := (nat_decl X A)(at level 90).
Notation "'BOOL' X ::= A" := (bool_decl X A)(at level 90).
Notation "'STR' X ::= A " := (str_decl X A) (at level 90).
Notation "X n:= A" := (nat_assign X A)(at level 90).
Notation "X b:= A" := (bool_assign X A)(at level 90).
Notation "X s:= A" := (str_assign X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation " 'While' '(' A ')' '{' S '}' 'End' " := (while A S) (at level 97).
Notation "'FOR' ( A ; B ; C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'If' B 'Then' '(' S ')'  'End'" := (ifthenelse B S) (at level 97).
Notation "'If' B 'Then' '(' S1 ')' 'Else' '(' S2 ')' 'End'" := (ifthenelse B S1 S2) (at level 97).



Check
  NAT "a" ::= 27 ;; NAT "b" ::= 3 ;; NAT "r" ::= 0 ;;
  While ("b") 
     { "r" n:= "a" %' "b" ;;
       "a" n:= "b" ;;
       "b" n:= "r" }
  End.

(*Check
    NAT "sum" ::= 0 ;;
    fors ( (NAT "i" ::= 0) ~ "i" <=' 6 ~ "i" n:= "i" +++ ) {
      "sum" :n= "sum" +' "i" }
.

Check 
     STR "n" ::= "homework" ;;
     NAT "x" ::= 10 ;;
     NAT "L" ;; "L" n:= len["n"] ;;
  If ("L")
      Then ( "L" n:= "x" )
      Else ( "L" n:= 0 )
  End.
  
*)


























