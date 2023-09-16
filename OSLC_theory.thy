theory OSLC_theory
  imports ZF
begin

consts 
  S :: "i" (* The set of servers*)
  R :: "i" (* The set of resources*)
  P :: "i" (* The set of properties*)
  L :: "i" (* The set of literals*)

definition 
  V :: "i" where
"V \<equiv> R \<union> L"  (* V is a property value, which can be a resource or a literal *)

(* Predicate that captures the relationship "s implements resource r" *)
consts 
  implements :: "[i, i] => o" (* This is a predicate taking two sets and returning a truth value *)

(* i=(s,r) in I means server implements resource r*)
definition 
  I :: "i" where
"I \<equiv> {p \<in> S \<times> R. implements(fst(p), snd(p))}"  
(* I is the set of all pairs (s, r) such that s implements r *)

(* Predicate capturing the relationship "resource r has the property p with value v" *)
consts 
  has_property_with_value :: "[i, i, i] => o"
(*
definition 
  T :: "i" where
"T \<equiv> {x \<in> R \<times> (P \<times> V). has_property_with_value(fst(x), snd(x), thd(x))}
"*)

end