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

Inductive Pointer :=
 | NULL : Pointer
 | pointer : string -> Pointer
 | reference : string -> Pointer .

(* in C un pointer poate fi asignat/declarat doar cu trei tipuri de valori: un alt pointer, referinta unei variabile
sau NULL*)

Scheme Equality for Pointer.

Coercion num: nat >-> ErrNat.
Coercion boolean: bool >-> ErrBool.
Coercion str: string >-> ErrString.
Coercion pointer: string >-> Pointer.




Check 7.
Check false.
Check "x".

(*String expressions *)

Inductive STRexp :=
 | str_err : ErrString -> STRexp
 | str_const : ErrString -> STRexp
 | str_var : string -> STRexp
 | strcmp : STRexp -> STRexp -> STRexp
 | strcat : STRexp -> STRexp -> STRexp.

Coercion str_var : string >-> STRexp.
Coercion str_err : ErrString >-> STRexp.



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
| strlen : STRexp -> AExp.


Coercion anum: ErrNat >-> AExp.
Coercion avar: string >-> AExp. 



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
| b_dif : AExp -> AExp -> BExp
| b_not : BExp -> BExp
| b_and : BExp -> BExp -> BExp
| b_or : BExp -> BExp -> BExp
| b_xor : BExp -> BExp -> BExp.

Coercion b_var : string >-> BExp.
Coercion b_err : ErrString >-> BExp.



(*Arrays*)


Inductive ErrArray :=
 | err_array : ErrArray
 | array_n : string -> nat -> (list nat) -> ErrArray
 | array_b : string -> nat -> (list bool) -> ErrArray
 | array_s : string -> nat -> (list string) -> ErrArray.
 


(* Array operations *)

Inductive ARRAY_exp :=
 | arr_const : ErrArray -> ARRAY_exp
 | arr_var : string -> ARRAY_exp
 | elem : ErrArray -> nat -> ARRAY_exp
 | delete : string -> nat -> ARRAY_exp
 | first_elem : ErrArray -> ARRAY_exp
 | last_elem : ErrArray -> ARRAY_exp.


(*Statements*)

Inductive Statement :=
  | nat_decl: string -> AExp -> Statement 
  | bool_decl: string -> BExp -> Statement 
  | str_decl : string -> STRexp -> Statement
  | array_decl : ErrArray -> Statement
  | ptr_nat_decl : string -> string -> Statement
  | ptr_bool_decl : string -> string -> Statement
  | ptr_string_decl : string -> string -> Statement
  | ref_decl : string -> string -> Statement
  | nat_assign : string -> AExp -> Statement 
  | bool_assign : string -> BExp -> Statement
  | str_assign : string -> STRexp -> Statement
  | ptr_assign_n : string -> AExp -> Statement
  | ptr_assign_b : string -> BExp -> Statement
  | ptr_assign_s : string -> STRexp -> Statement
  | ref_assign : string -> string -> Statement
  | get_elem_array : string -> nat -> Statement
  | sequence : Statement  -> Statement  -> Statement 
  | cin : string -> Statement (*input -> variable *)
  | cout : STRexp -> Statement
  | while : BExp -> Statement -> Statement
  | for_new : Statement -> BExp -> Statement -> Statement -> Statement
  | ifthen : BExp -> Statement -> Statement
  | ifthenelse : BExp -> Statement -> Statement -> Statement
  | empty : Statement (*bloc gol*)
  | break : Statement
  | continue : Statement
  | switchcase : AExp -> list Case -> Statement
  | fun_call : string -> (list string) -> Statement (*apel de functie cu o serie de parametrii *)
   with Case :=
    | case_default : Statement -> Case
    | case : ErrNat -> Statement -> Case.



Inductive Types :=
  | err : Types
  | err_undecl : Types 
  | err_assign : Types 
  | default : Types 
  | val_nat : ErrNat -> Types (*valorile pe care le atribui unei variabile declarate  nat*)
  | val_bool : ErrBool -> Types 
  | val_string : ErrString -> Types 
  | val_pointer : nat -> bool -> Types
  | val_array : ErrArray -> Types
  | code : Statement -> Types. (* function code  *)


Coercion val_nat : ErrNat >-> Types.
Coercion val_bool : ErrBool >-> Types.
Coercion val_string : ErrString >-> Types.
Coercion val_array : ErrArray >-> Types.
Coercion code : Statement >-> Types.

Definition get_statement (cod : Types) : Statement :=
match cod with
| code statement => statement
| _ => empty
end.



(*Inductive type for functions *)

Inductive Pgm :=
| secv : Pgm -> Pgm -> Pgm (*Secventa de funcii si/sau declaratii de variabile *)
| default_nat_decl : string -> Pgm 
| default_bool_decl : string -> Pgm 
| default_string_decl : string -> Pgm 
| default_array_decl : string -> nat -> Pgm 
| default_ptr_decl : string -> Pgm 
| main : Statement -> Pgm 
| function : string -> list string -> Statement -> Pgm. 



Definition type_equality  (t1 : Types)(t2 : Types) : bool :=
 match t1 with 
 | err => match t2 with
         | err => true
         | _ => false
         end
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
 | val_pointer p1 p2 => match t2 with
                    | val_pointer p1' p2' => true
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




Definition Memory := nat -> Types.
Definition Adress := string -> nat.
Inductive MemLayer := 
| pair : Adress -> Memory -> nat -> Adress -> Memory -> nat -> MemLayer.
Notation "{< A1 , M1 , N1 >} -> {< A2 , M2 , N2 >}" := (pair A1 M1 N1 A2 M2 N2) (at level 0).




Definition local (m : MemLayer) (v : string) : bool :=
match m with
| pair adr1 mem1 _ adr2 mem2 _ => if (type_equality ( mem1 (adr1 v) ) err) 
                              then false 
                              else true
end.

Definition get_value (m : MemLayer) (v : string) : Types :=
match m with
| pair adr1 mem1 _ adr2 mem2 _ => if (local m v) 
                              then mem1(adr1 v) 
                              else mem2(adr2 v)
end.

Definition pointer_adress (a : Types) : nat :=
match a with
| val_pointer p _ => p
| _ => 0
end.

Definition pointer_value (m : MemLayer) (p : string) : Types :=
let pointer := get_value m p in
match pointer with
| val_pointer val local => match m with
                    | pair _ mem1 _ _ mem2 _ => if (local) 
                                                then (mem1 (pointer_adress pointer) )
                                                else (mem2 (pointer_adress pointer) )
                    end 
| _ => err
end.

Definition get_local_top (m : MemLayer) : nat :=
match m with
| pair _ _ maxval _ _ _  => maxval
end.

Definition get_global_top (m : MemLayer) : nat :=
match m with
| pair _ _ _ _ _ maxval  => maxval
end.

Definition get_adress (m : MemLayer) (v : string) : nat :=
match m with
| pair adr1 _ _ adr2 _ _ => if (Nat.eqb (adr1 v) 0) 
                            then adr2 v 
                             else adr1 v
end.

Definition get_local_adress (m : MemLayer) (v : string) : nat :=
match m with
| pair adress _ _ _ _ _ => adress v
end.

Definition get_global_adress (m : MemLayer) (v : string) : nat :=
match m with
| pair _ _ _ adress _ _ => adress v
end.

Definition update_adress (st : Adress) (v : string) (n : nat) : Adress := 
fun x => if (string_beq x v) 
         then n 
         else st x.

Definition update_memory (mem : Memory) (n : nat) (val : Types) : Memory :=
fun n' => if (Nat.eqb n' n) 
          then val 
          else mem n'. 


Definition update_local_mem (M : MemLayer) (V : string) (T : Types) (nr : nat) : MemLayer :=
match M with
|{<adr1, mem1, top1>} -> {<adr2, mem2, top2>} 
      => 
          if (andb (Nat.eqb nr (get_local_adress M V) ) (Nat.eqb nr 0) ) 
          then {<adr1, mem1, top1>} -> {<adr2, mem2, top2>} 
          else {<update_adress adr1 V nr, update_memory mem1 nr T, 
            (if (Nat.ltb nr top1) then top1 else Nat.add top1 1)>} -> {<adr2, mem2, top2>}
end.

Definition update_global_mem (M : MemLayer) (V : string) (T : Types) (nr : nat) : MemLayer :=
match M with
|{<adr1, mem1, top1>} -> {<adr2, mem2, top2>} 
    => 
      if (andb (Nat.eqb nr (get_global_adress M V) ) (Nat.eqb nr 0) ) 
      then {<adr1, mem1, top1>} -> {<adr2, mem2, top2>} 
       else
       {<adr1, mem1, top1>} -> {<update_adress adr2 V nr, update_memory mem2 nr T, 
      (if (Nat.ltb nr top2) then top2 else Nat.add top2 1) >}
end.

Definition update_local_at_adress (M : MemLayer) (addr : nat) (T : Types): MemLayer :=
match M with
|{<adr1, mem1, top1>} -> {<adr2, mem2, top2>}
     => 
     if (Nat.eqb addr 0) 
     then {<adr1, mem1, top1>} -> {<adr2, mem2, top2>} 
     else {<adr1, update_memory mem1 addr T, top1 >} -> {<adr2, mem2, top2>}
end.

Definition update_global_at_adress (M : MemLayer) (addr : nat) (T : Types): MemLayer :=
match M with
|{<adr1, mem1, top1>} -> {<adr2, mem2, top2>} 
     => 
     if (Nat.eqb addr 0) 
     then {<adr1, mem1, top1>} -> {<adr2, mem2, top2>}
     else {<adr1, mem1, top1>} -> {<adr2, update_memory mem2 addr T, top2 >}
end.

Definition update_at_adress (M : MemLayer) (addr : nat) (T : Types) : MemLayer :=
match M with
|{<adr1, mem1, top1>} -> {<adr2, mem2, top2>} 
      =>  
       if (type_equality (mem1 addr) err)
       then update_global_at_adress M addr T
       else update_local_at_adress M addr T
end.

Definition mem_default : Memory := fun x => err.
Definition adress_default : Adress := fun x => 0.
Definition stack_default := {<adress_default, mem_default, 1>} -> {<adress_default, mem_default, 1>}.

Definition stack_local (m : MemLayer) : MemLayer :=
match m with
| {<adr1, mem1, top1>} -> {<adr2, mem2, top2>} => {<adress_default, mem_default, 1>} -> {<adr2, mem2, top2>}
end.


(*Operations with strings *)

Definition str_length (s : ErrString) : ErrNat :=
 match s with 
  | err_string => err_nat
  | str s1 => num (length s1)
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

Definition Strlen (s : Types) :=
match s with
| val_string s1 => ( str_length s1 )
| _ => err
end.

Definition Strcat (s1 s2 : Types) := 
match s1, s2 with
| val_string s1', val_string s2' => match s1', s2' with
                                    | str x, str y =>  ( str_cat x y )
                                    | _, _ => err_string
                                     end
| _, _ => err
end.

Definition Strcmp (s1 s2 : Types) := 
match s1, s2 with
| val_string s1', val_string s2' => match s1', s2' with
                                    | str x, str y =>  ( str_cmp x y )
                                    | _, _ => err_string
                                     end
| _, _ => err
end.


(*Notations for string operations*)

Notation " len[ S ] " := (strlen S) (at level 31).
Notation " S1 /+/ S2 " := (strcat S1 S2) (at level 30).
Notation " S1 ? S2 " := (strcmp S1 S2) (at level 32).


(*Semantics for string operations*)

Reserved Notation "STR '=S[' St ']=>' N" (at level 60).
Inductive streval_fun : STRexp -> MemLayer -> Types -> Prop :=
| s_const : forall s sigma, str_const s =S[ sigma ]=> val_string s
| s_var : forall s sigma, str_var s =S[ sigma ]=> get_value sigma s
| s_cmp : forall s1 s2 sigma s str1 str2,
    s1 =S[ sigma ]=> str1 ->
    s2 =S[ sigma ]=> str2 ->
    s = Strcmp str1 str2 ->
    s1 ? s2  =S[ sigma ]=> s
| s_cat : forall s1 s2 sigma s st1 st2,
    s1 =S[ sigma ]=> st1 ->
    s2 =S[ sigma ]=> st2 ->
    s =Strcat st1 st2 ->
    s1 /+/ s2 =S[ sigma ]=> s
where "STR '=S[' St ']=>' N" := (streval_fun STR St N).

(*Semantics for Arrays*)

Definition get_elem (a : ErrArray) (nr : nat) : Types :=
match a with
| array_n s n l => val_nat (List.nth nr l 0)  
| array_b s n l => val_bool (List.nth nr l false) 
| array_s s n l => val_string (List.nth nr l "") 
| err_array => err_undecl
end.

Definition get_last_elem (a : ErrArray) : Types :=
match a with 
| array_n s n l => val_nat (List.last l 0)
| array_b s n l => val_bool (List.last l false)
| array_s s n l => val_string (List.last l "")
| err_array => err_undecl
end.
Definition delete_elem (a : ErrArray) (nr : nat) : Types :=
match a with
| array_n s n l => val_array (array_n s n (List.remove eq_nat_dec (List.nth nr l 0) l))
| array_b s n l => val_array (array_b s n (List.remove bool_dec (List.nth nr l false) l))
| array_s s n l => val_array (array_s s n (List.remove string_dec (List.nth nr l "") l))
| err_array => err_undecl
end.




(*Reserved Notation "ARR '~[' St ']~>' N" (at level 60).
Inductive array_eval: ARRAY_exp -> MemLayer -> Types -> Prop :=
| arr_Const: forall a sigma ,
  arr_const a ~[ sigma ]~> val_array a
| arr_Var: forall a sigma mem ,
  arr_var a ~[ sigma ]~> (mem(sigma a))
| arr_elem: forall a nr rez sigma ,
   rez = (get_elem a nr)
 ( elem a nr) ~[ sigma ]~> rez
where "ARR '~[' St ']~>' N" := (array_eval ARR St N).*)




(*Arithmetic operations *)

Definition plus_err (a b : Types) :=
match a, b with
| val_nat x, val_nat y => match x, y with
                        | num n1, num n2 => num (n1 + n2)
                        | _, _ => err_nat
                        end
| _ , _ => err
end.

Definition minus_err (a b : Types) :=
match a, b with
| val_nat x, val_nat y => match x, y with
                        | num n1, num n2 => if (ltb n1 n2) then err_nat else num (n1 - n2)
                        | _, _ => err_nat
                        end
| _ , _ => err
end.

Definition mul_err (a b : Types) :=
match a, b with
| val_nat x, val_nat y => match x, y with
                        | num n1, num n2 => num (n1 * n2)
                        | _, _ => err_nat
                        end
| _ , _ => err
end.

Definition div_err (a b : Types) :=
match a, b with
| val_nat x, val_nat y => match x, y with
                        | num n1, num n2 => if (Nat.eqb n2 0) then err_nat else num (div n1 n2)
                        | _, _ => err_nat
                        end
| _ , _ => err
end.

Definition mod_err (a b : Types) :=
match a, b with
| val_nat x, val_nat y => match x, y with
                        | num n1, num n2 => if (Nat.eqb n2 0) then err_nat else num (modulo n1 n2)
                        | _, _ => err_nat
                        end
| _ , _ => err
end.

Definition inc (a : Types) :=
match a with
| val_nat x => match x with
                        | num n1 => num (n1 + 1)
                        | _ => err_nat
                        end
| _ => err
end.

Definition dec (a : Types) :=
match a with
| val_nat x => match x with
                        | num n1 => if (Nat.eqb n1 0) then err_nat else num (n1 - 1)
                        | _ => err_nat
                        end
| _  => err
end.

(*Notations for arithmetic expressions*)

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (aminus A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "A +++" := (ainc A) (at level 40,left associativity).
Notation "A ---" := (adec A) (at level 49). 


(*Semantics for arithmetic expressions*)

Reserved Notation "A =[ S ]=> N" (at level 65).
Inductive aeval_fun : AExp -> MemLayer -> Types -> Prop :=
| e_const : forall n sigma, anum n =[ sigma ]=> val_nat n
| e_avar : forall v sigma, avar v =[ sigma ]=> get_value sigma v
| e_add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = plus_err i1 i2 ->
    a1 +' a2 =[ sigma ]=> n
| e_minus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = minus_err i1 i2 ->
    a1 -' a2 =[ sigma ]=> n
| e_mul : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mul_err i1 i2 ->
    a1 *' a2 =[ sigma ]=> n
| e_div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = div_err i1 i2 ->
    a1 /' a2 =[ sigma ]=> n
| e_mod : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mod_err i1 i2 ->
    a1 %' a2 =[ sigma ]=> n
| e_inc : forall a1 i1 sigma n,
    a1 =[ sigma ]=> i1 ->
    n = inc i1 ->
    a1 +++  =[ sigma ]=> n
| e_dec : forall a1 i1 sigma n,
    a1 =[ sigma ]=> i1 ->
    n = dec i1 ->
    a1 ---  =[ sigma ]=> n
| e_strlen : forall a1 sigma s1 n,
    a1 =S[ sigma ]=> s1 ->
    n = Strlen s1 ->
    len[ a1 ] =[ sigma ]=> n
where "a =[ sigma ]=> n" := (aeval_fun a sigma n).


(*Boolean operations*)


Definition less_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_nat b1', val_nat b2' => match b1', b2' with
                                 | num x, num y  => boolean (Nat.ltb x y)
                                 | _, _ => err_bool
                                 end
  |_, _ => err
  end.

Definition more_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_nat b1', val_nat b2' => match b1', b2' with
                                 | num x, num y  => boolean (negb (Nat.ltb x y))
                                 | _, _ => err_bool
                                 end
  |_, _ => err
  end.

Definition less_eq_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_nat b1', val_nat b2' => match b1', b2' with
                                 | num x, num y  => boolean (Nat.leb x y)
                                 | _, _ => err_bool
                                 end
  |_, _ => err
  end.


Definition more_eq_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_nat b1', val_nat b2' => match b1', b2' with
                                 | num x, num y  => boolean (negb(Nat.leb x y))
                                 | _, _ => err_bool
                                 end
  |_, _ => err
  end.


Definition equal_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_nat b1', val_nat b2' => match b1', b2' with
                                 | num x, num y  => boolean (Nat.eqb x y)
                                 | _, _ => err_bool
                                 end
  |_, _ => err
  end.

Definition dif_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_nat b1', val_nat b2' => match b1', b2' with
                                 | num x, num y  => boolean (negb (Nat.eqb x y))
                                 | _, _ => err_bool
                                 end
  |_, _ => err
  end.



Definition not_err (b1 : Types) : Types :=
  match b1 with
  | val_bool b1' => match b1' with
                   | boolean x => boolean (negb x)
                   | _ => err_bool
                     end
  |_ => err
  end.


Definition and_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_bool b1', val_bool b2' => match b1', b2' with
                                 | boolean x, boolean y  => boolean (andb x y)
                                 | _, _ => err_bool
                                 end
  |_, _ => err
  end.

Definition or_err (b1 b2 : Types) : Types :=
  match b1, b2 with
  | val_bool b1', val_bool b2' => match b1', b2' with
                                 | boolean x, boolean y  => boolean (orb x y)
                                 | _, _ => err_bool
                                 end
  |_, _ => err
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

Definition Xor (b1 b2 : Types) : Types := 
match b1, b2 with
| val_bool b1', val_bool b2' => match b1', b2' with
                              | boolean x, boolean y => val_bool (xorb_err x y)
                              | _, _ => err_bool
                              end
| _, _ => err
end.



(*Semantics for boolean expressions*)

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval_fun : BExp -> MemLayer -> Types -> Prop :=
| e_true : forall sigma, b_true ={ sigma }=> boolean true
| e_false : forall sigma, b_false ={ sigma }=> boolean false
| e_bvar : forall v sigma, b_var v ={ sigma }=> get_value sigma v
| e_less : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = less_err i1 i2 ->
   b_less a1 a2 ={ sigma }=> b
| e_more : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = more_err i1 i2 ->
   b_more a1 a2 ={ sigma }=> b
| e_less_eq : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = less_eq_err i1 i2 ->
   b_less_eq a1 a2 ={ sigma }=> b
| e_more_eq : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = more_eq_err i1 i2 ->
    b_more_eq a1 a2 ={ sigma }=> b
| e_equal: forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = equal_err i1 i2 ->
    b_equal a1 a2 ={ sigma }=> b
| e_dif : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = dif_err i1 i2 ->
    b_dif a1 a2 ={ sigma }=> b
| e_not_true : forall b sigma,
    b ={ sigma }=> boolean true ->
    b_not b ={ sigma }=> boolean false
| e_not_false : forall b sigma,
    b ={ sigma }=> boolean false ->
    b_not b ={ sigma }=> boolean true
| e_and_true : forall b1 b2 sigma t,
    b1 ={ sigma }=> boolean true ->
    b2 ={ sigma }=> t ->
    b_and b1 b2 ={ sigma }=> t
| e_and_false : forall b1 b2 sigma,
    b1 ={ sigma }=> boolean false ->
    b_and b1 b2 ={ sigma }=> boolean false
| e_or : forall b1 b2 sigma t t1 t2,
    b1 ={ sigma }=> t1 ->
    b2 ={ sigma }=> t2 ->
    t = or_err t1 t2 ->
   b_or b1 b2 ={ sigma }=> t
| e_xorb : forall b1 b2 sigma t t1 t2,
    b1 ={ sigma }=> t1 ->
    b2 ={ sigma }=> t2 ->
    t = Xor t1 t2 ->
   b_xor b1 b2 ={ sigma }=> t
where "B ={ S }=> B'" := (beval_fun B S B').


Definition to_bool (b : Types) : bool :=
match b with
| val_bool b' => match b' with
                 |boolean true => true
                 |boolean false => false
                 |errBool => false
                 end
| _ => false
end.

Notation "'default:{' S };" := (case_default S) (at level 97).
Notation "'case(' X ):{ S };" := (case X S) (at level 97).

Definition get_case_Stmt (C : Case) : Statement :=
match C with
| default:{ s }; => s
| case( _ ):{ s }; => s
end.

Definition check_case (C : Case ) (n : Types) : bool :=
match C with
| default:{ _ }; => true
| case( a ):{ _ }; => to_bool (equal_err a n)
end.

Fixpoint execute_switchcase (n : Types) (cl : list Case) : Statement :=
match n with
| val_nat n' => match cl with 
              | nil => empty
              | x :: next => if (check_case x n) then (get_case_Stmt x) else (execute_switchcase n next)
              end
| _ => empty
end.


Reserved Notation " L -{ M , S }-> M' , S'" (at level 60).
Inductive eval_fun : Statement -> MemLayer -> MemLayer -> MemLayer -> MemLayer -> Prop :=
| e_nat_decl : forall s x value sigma sigma' new,
    value =[ sigma ]=> x ->
    sigma' = update_local_mem sigma s x (get_local_top sigma) ->
    ( nat_decl s value )-{ sigma , new }-> sigma' , new
| e_bool_decl : forall s b value sigma sigma' new,
    value ={ sigma }=> b ->
    sigma' = update_local_mem sigma s b (get_local_top sigma) ->
    ( bool_decl s value)-{ sigma , new }-> sigma' , new
| e_str_decl : forall s value sigma sigma' str new,
    value =S[ sigma ]=> str ->
    sigma' = update_local_mem sigma s str (get_local_top sigma) ->
    ( str_decl s value )-{ sigma , new }-> sigma' , new
| e_ptr_nat_decl : forall P V sigma sigma' loc new,
    type_equality (get_value sigma V) (val_nat 0) = true ->
    loc = local sigma V ->
    sigma' = update_local_mem sigma P (val_pointer (get_adress sigma V) loc) (get_local_top sigma) ->
    ( ptr_nat_decl P V )-{ sigma , new }-> sigma', new
| e_ptr_bool_decl : forall P V sigma sigma1 loc new,
    type_equality (get_value sigma V) (val_bool false) = true ->
    loc = local sigma V ->
    sigma1 = update_local_mem sigma P (val_pointer (get_adress sigma V) loc) (get_local_top sigma) ->
    ( ptr_bool_decl P V )-{ sigma , new }-> sigma1 , new
| e_ptr_string_decl : forall P V sigma sigma1 loc new,
    type_equality (get_value sigma V) (val_string ("") ) = true ->
    loc = local sigma V -> 
    sigma1 = update_local_mem sigma P (val_pointer (get_adress sigma V) loc) (get_local_top sigma) ->
    ( ptr_string_decl P V )-{ sigma , new }-> sigma1 , new
(* |e_array_decl
   | e_ref_decl*)
| e_nat_assign : forall s x value sigma sigma' new,
    type_equality (get_value sigma s) (val_nat 0) = true ->
    value =[ sigma ]=> x ->
    sigma' = update_at_adress sigma (get_adress sigma s) x ->
    ( nat_assign s value )-{ sigma , new }-> sigma' , new
| e_bool_assign : forall s b value sigma sigma' new,
    type_equality (get_value sigma s) (val_bool false) = true ->
    value ={ sigma }=> b ->
    sigma' = update_at_adress sigma (get_adress sigma s) b ->
    ( bool_assign s value )-{ sigma , new }-> sigma' , new
| e_str_assign : forall s value sigma sigma' sstr new,
    type_equality (get_value sigma s) (val_string ("") ) = true ->
    value =S[ sigma ]=> sstr ->
    sigma' = update_at_adress sigma (get_adress sigma s) sstr  ->
    ( str_assign s value )-{ sigma , new }-> sigma' , new 
| e_ptrassign_n : forall V E i1 sigma sigma1 new,
    type_equality (get_value sigma V) (val_pointer 0 false) = true ->
    E =[ sigma ]=> i1 ->
    sigma1 = update_at_adress sigma (pointer_adress (get_value sigma V) ) i1  ->
    ( ptr_assign_n V E )-{ sigma , new }-> sigma1, new
| e_ptrassign_b : forall V E i1 sigma sigma1 new,
    type_equality (get_value sigma V) (val_pointer 0 false) = true ->
    E ={ sigma }=> i1 ->
    sigma1 = update_at_adress sigma (pointer_adress (get_value sigma V) ) i1 ->
   ( ptr_assign_b V E )-{ sigma , new }-> sigma1 , new
| e_ptrassign_s : forall V E i1 sigma sigma1 new,
    type_equality (get_value sigma V) (val_pointer 0 false) = true ->
    E =S[ sigma ]=> i1 ->
    sigma1 = update_at_adress sigma (pointer_adress (get_value sigma V) ) i1  ->
   ( ptr_assign_s V E )-{ sigma , new }-> sigma1 , new
(*|e_ref_assign*)
| e_sequence : forall s1 s2 sigma sigma' sigma'' new new',
   ( s1 )-{ sigma , new }-> sigma' , new ->
   ( s2 )-{ sigma' , new }-> sigma'' , new' ->
   (sequence s1 s2 )-{ sigma , new }-> sigma'' , new'
| e_while_false : forall b s sigma new,
    b ={ sigma }=> false ->
    ( while b s )-{ sigma , new }-> sigma , new
| e_while_true : forall b s sigma sigma' new,
    b ={ sigma }=> true ->
    ( sequence s ( while b s ) )-{ sigma , new }-> sigma' , new ->
    ( while b s )-{ sigma , new }-> sigma' , new
| e_for_false : forall s b s1 s2 sigma sigma' new,
    ( s )-{ sigma, new }-> sigma', new ->
    b ={ sigma' }=> false ->
    ( for_new s b s1 s2 )-{ sigma , new }-> sigma' , new
| e_for_true : forall s b s1 s2 sigma sigma' sigma'' new,
    ( s )-{ sigma , new }-> sigma', new ->
    (while b ( sequence s2 s1) )-{ sigma' , new }-> sigma'' , new ->
    ( for_new s b s1 s2 )-{ sigma , new }-> sigma'' , new
| e_ifthen_false : forall b s1 sigma new,
    b ={ sigma }=> false ->
    ( ifthen b s1 )-{ sigma , new }-> sigma , new
| e_ifthen_true : forall b s1 sigma sigma' new,
    b ={ sigma }=> true ->
    ( s1 )-{ sigma , new }-> sigma' , new ->
    ( ifthen b s1 )-{ sigma , new }-> sigma' , new
| e_ifthenelse_false : forall b s1 s2 sigma sigma' new,
    b ={ sigma }=> false ->
    ( s2 )-{ sigma , new }-> sigma' , new ->
    ( ifthenelse b s1 s2 )-{ sigma , new }-> sigma' , new
| e_ifthenelse_true : forall b s1 s2 sigma sigma' new,
    b ={ sigma }=> true ->
    ( s1 )-{ sigma , new }-> sigma' , new ->
    ( ifthenelse b s1 s2 )-{ sigma , new }-> sigma' , new
| e_empty : forall sigma new,
   ( empty )-{ sigma , new }-> sigma , new
| e_break: forall sigma new,
   ( break ) -{ sigma, new }-> sigma , new
| e_break_case1 : forall b s n sigma new,
    b ={ sigma }=> true ->
    n = ( sequence break s) ->
    ( sequence s ( while b n) ) -{ sigma, new }-> sigma, new ->
    while b n -{ sigma, new }-> sigma, new
| e_break_case2 : forall b s n sigma sigma' new,
    b ={ sigma }=> true ->
    n = ( sequence s break) ->
    ( sequence s ( while b n)) -{ sigma, new }-> sigma' , new
(*|e_continue*)
| e_switchcase : forall a c sigma n v sigma' new,
    a =[ sigma ]=> n ->
    v = (execute_switchcase n c) ->
    v -{ sigma , new }-> sigma' , new ->
   ( switchcase a c ) -{ sigma , new }-> sigma' , new
| e_fun_call : forall s l stmt sigma sigma' new,
    stmt = get_statement (get_value sigma s ) ->
    ( stmt )-{ stack_local sigma , sigma}-> sigma' , new ->
    ( fun_call s l )-{ sigma , new }-> sigma' , new
where "L -{ M , S }-> M' , S'" := (eval_fun L M S M' S').



(*Notations for boolean expressions*)

Notation "A <' B" := (b_less A B) (at level 53).
Notation "A >' B" := (b_more A B) (at level 53).
Notation "A <=' B" := (b_less_eq A B) (at level 53).
Notation "A >=' B" := (b_more_eq A B) (at level 53).
Notation "A == B" := (b_equal A B) (at level 53).
Notation "A <!> B" := (b_dif A B) (at level 53).
Notation " ! A " := (b_not A) (at level 71).
Notation "A & B" := (b_and A B) (at level 75).
Notation "A | B" := (b_or A B) (at level 75).
Notation "A ^^ B" := (b_xor A B) (at level 60).


(*Notations for arrays*)
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.


Notation "Array'::= A" := (array_decl A ) (at level 58). 

Notation " A '[[' X ']]' n->  L  " := (array_n A X L) (at level 30).
Notation " B '[[' X ']]' b->  L  " := (array_b B X L) (at level 30).
Notation " S '[[' X ']]' s->  L  " := (array_s S X L) (at level 30).

Notation " s [[' i ']] " := (elem s i)(at level 22).




(*Notations for statements & functions *)

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
Notation "X p:= 'n*' A" := (ptr_assign_n X A)(at level 90).
Notation "X p:= 'b*' A" := (ptr_assign_b X A)(at level 90).
Notation "X p:= 's*' A" := (ptr_assign_s X A)(at level 90).
Notation "X r:= '&&' A" := (ref_assign X A)(at level 90).


Notation "V [ P ]" := (get_elem_array V P)(at level 79).

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
Notation "'int' 'main()' { }" := (main empty)(at level 95).
Notation "'int' F (){ S }" := (function F nil S)(at level 90).
Notation "'int' F (){ }" := (function F nil empty)(at level 95).
Notation "'int' F (( p_1 , .. , p_n )){ S }" := (function F (cons p_1 .. (cons p_n nil) .. ) S)(at level 90).
Notation "'int' F (( p_1 , .. , p_n )){ }" := (function F (cons p_1 .. (cons p_n nil) .. ) empty)(at level 95).


Notation "'cin>>(' I )" := (cin I) (at level 92).
Notation "'cout<<(' O )" := (cout O) (at level 92).

Notation "'f_call' F (( p_1 , .. , p_n ))" := (fun_call F (cons p_1 .. (cons p_n nil) .. ) ) (at level 89).
Notation "'f_call' F (( ))" := (fun_call F nil) (at level 89).


(*Semantics for statements*)


(*EXAMPLES*)
(*String operations *)

Check ("Info " /+/ "PLP") .
Check (len[ "Proiect" ]).
Check ("ab" ? "ba").

(*Arithmetic expressions *)

Check (2 +' 3 *' 5).
Check (2 +' 3 *' "n").
Check ("sum" /' "sum"---).
Check ("i" +++).
Check (3 %' 0).

(*Boolean expressions *)

Check ( 3 >=' ("x" /' 0) ) .
Check ( ( ("a" +' 5) /' ( ("b" -'1) *' 3) ) <=' 100 ).
Check ( ( ! b_false ) & b_true).
Check ( b_true | b_false | "sum" | ("a" <=' "b") ).
Check (b_true ^^ b_false).
Check ("a" ^^ "b").

(*Arrays*)
Check  [1 , 3 , 5 , 8].
Check [].
Check [true , false].
Check ["proiect" , "PLP"].

Check Array'::= "a" [[10]] n-> [1, 2].

Check "x"[[2]] n-> [ 0, 1].
Check "booleans"[[3]] b-> [true,true,false].
Check "homework"[[2]] s-> ["project", "syntax"].




(*Statements*)

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

Check ( "nat_pointer" := NAT** "n") ;; ( "n" p:= n* "p")  .
Check ( "bool_pointer" := BOOL** "bool") ;; ( "bool" r:= && "b_true").
Check  ( "string_pointer" := STR** "str")  ;; ("str" r:= && "syntax").

Check (BOOL "new" ::= b_false) ;;
      ( "new" p:=b* "ok" ) ;; ("ok" r:= && "new").


(*SEMANTICS*)

Definition stack_1 := update_local_mem stack_default "x" (num 3) (get_local_top stack_default).
Definition stack_2 := update_local_mem stack_1 "y" (num 5) (get_local_top stack_1).
Compute get_local_adress stack_2 "x".
Compute get_local_adress stack_2 "y".


Example ex_1 : "x" +' "y" =[ stack_2 ]=> val_nat 8.
Proof.
  eapply e_add.
  -eapply e_avar.
    -simpl.
    +eapply e_avar.
    -simpl. reflexivity.
Qed.







