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
 | nat_pointer : nat -> ErrPointer
 | bool_pointer : nat -> ErrPointer
 | str_pointer : nat -> ErrPointer.



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
| ptr_nat : string -> AExp
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
| ptr_bool : string -> BExp
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
 | ptr_string : string -> STRexp
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
 | insert : ErrArray -> Array_opp
 | delete : ErrArray -> Array_opp
 | min : ErrArray -> Array_opp
 | max : ErrArray -> Array_opp.



(*Statements*)

Inductive Statement :=
  | nat_decl: string -> AExp -> Statement 
  | ptr_nat_decl : string -> string -> Statement
  | bool_decl: string -> BExp -> Statement 
  | ptr_bool_decl : string -> string -> Statement
  | str_decl : string -> STRexp -> Statement
  | ptr_string_decl : string -> string -> Statement
  | array_decl_n : string -> nat -> Statement
  | array_decl_b : string -> nat  -> Statement
  | array_decl_s : string -> nat -> Statement
  | nat_assign : string -> AExp -> Statement 
  | ptr_nat_assign : string -> AExp -> Statement 
  | bool_assign : string -> BExp -> Statement
  | ptr_bool_assign : string -> BExp -> Statement
  | str_assign : string -> string -> Statement
  | ptr_string_assign : string -> STRexp -> Statement
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
    | case_x : AExp -> Statement -> Case .






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
| default_array_decl : string -> Pgm
| main : Statement -> Pgm (* main function - no parameters *)
| function : string -> list string -> Statement -> Pgm. (* functions *)



(* Default values types - used for variables of different types outside a function *)

(*Notations & examples for arithmetic expressions *)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (aminus A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "A +++" := (ainc A) (at level 40,left associativity).
Notation "A ---" := (adec A) (at level 49). 
Notation "'NAT*' X" := (ptr_nat X) (at level 0).


Check (2 +' 3 *' 5).
Check (2 +' 3 *' "n").
Check ("sum" /' "sum"---).
Check ("i" +++).
Check (3 %' 0).
Check ( NAT* "i").

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
Notation "'BOOL*' X" := (ptr_bool X) (at level 0).

Check ( 3 >=' ("x" /' 0)) .
Check (( ("a" +' 5) /' (("b" -'1) *' 3)) <=' 100 ).
Check (( ! b_false ) & b_true).
Check ( b_true | b_false | "sum" | ("a" <=' "b")).
Check (b_true ^^ b_false).
Check ("a" ^^ "b").
Check ( BOOL* "bool").


(*Notations & examples for string operations *)
Notation " len[ S ] " := (strlen S) (at level 31).
Notation " S1 /+/ S2 " := (strcat S1 S2) (at level 30).
Notation " S1 ? S2 " := (strcmp S1 S2) (at level 32).
Notation "'STR*' X" := (ptr_string X) (at level 0).

Check ("Info " /+/ "PLP") .
Check (len[ "Proiect" ]).
Check ("ab" ? "ba") .
Check ( STR* "string").


(*Notations & examples for arrays*)
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.


Check  [1 , 3 , 5 , 8].
Check [].
Check [true , false].
Check ["proiect" , "PLP"].

Notation "'Nat_array' A '[(' X ')]' " :=(array_decl_n A X)(at level 4).
Notation " A '[[' X ']]' n->  L  " := (array_assign_n A X L) (at level 30).

Notation "'Bool_array' B '[(' X ')]' " :=(array_decl_n B X)(at level 4).
Notation " B '[[' X ']]' b->  L  " := (array_assign_b B X L) (at level 30).


Notation "'Str_array' S '[(' X ')]' " :=(array_decl_s S X)(at level 4).
Notation " S '[[' X ']]' s->  L  " := (array_assign_s S X L) (at level 30).

Check Nat_array "x"[(2)].
Check Bool_array "booleans"[(3)].
Check Str_array "homework"[(2)].

Check "x"[[2]] n-> [ 0, 1].
Check "booleans"[[3]] b-> [true,true,false].
Check "homework"[[2]] s-> ["project", "syntax"].


(*Notations & examples for statements & functions *)
Notation "'NAT' X ::= A  " := (nat_decl X A)(at level 90).
Notation "'NAT**' X ::= A " := (ptr_nat_decl X A) (at level 90).

Notation "'BOOL' X ::= A " := (bool_decl X A)(at level 90).
Notation "'BOOL**' X ::= A " := (ptr_bool_decl X A) (at level 90).

Notation "'STR' X ::= A " := (str_decl X A) (at level 90).
Notation "'STR**' X ::= A " := (ptr_string_decl X A) (at level 90).

Notation "'Default_nat' X" := (default_nat_decl X) (at level 90).
Notation "'Default_bool' B" := (default_bool_decl  B) (at level 90).
Notation "'Default_str' S" := (default_string_decl S) (at level 90).
Notation "'Default_arr' V" := (default_array_decl V) (at level 90).

Notation "X n:= A" := (nat_assign X A)(at level 80).
Notation "X n*:= A" := (ptr_nat_assign X A) (at level 90). 

Notation "X b:= A" := (bool_assign X A)(at level 90).
Notation "X b*:= A" := (ptr_bool_assign X A) (at level 90). 

Notation "X s:= A" := (str_assign X A)(at level 90).
Notation "X s*:= A" := (ptr_string_assign X A) (at level 90). 



Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "S1 ;.; S2" := (secv S1 S2) (at level 93, right associativity).

Notation " 'While' '(' B ')' '{' S '}' 'End' " := (while B S) (at level 97).
Notation "'For' ( A ~ B ~ C ) 'Do' { S } 'End'" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'If' '(' B ')' 'Then' '(' S1 ')' 'Else' '(' S2 ')' 'End'" := (ifthenelse B S1 S2) (at level 97).
Notation "'If'(' B ) 'Then'{' S '}End'" := (ifthen B S) (at level 97).

Notation "'default:{' S };" := (case_default S) (at level 97).
Notation "'case(' X ):{ S };" := (case_x X S) (at level 97).
Notation "'switchcase'(' Y ){ case_1 .. case_n '}'" := (switchcase Y (cons case_1 .. (cons case_n nil) .. )) (at level 98).

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
       BOOL "rez" ::= ("sir1")
     }End.

Check switchcase (0) [ case_default ("a" n:= 0) ].
 
(*Check switchcase ( "x")
    { case( 5 ):{ "x" n:= 5 };
     default :{ "x" n:= 0 }
     }.
*)


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


Check (NAT** "nat_pointer" ::= "n") ;; ( "n" n*:= 0)  .
Check (BOOL** "bool_pointer" ::= "bool") ;; ( "bool" b*:= b_true).
Check  (STR** "string_pointer" ::= "str")  ;; ("str" s*:= "syntax").

Check (BOOL "new" ::= b_false) ;;
      ( "new" b*:= b_true ) ;; ("ok" s*:= "new").


























