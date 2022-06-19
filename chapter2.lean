import tactic.interactive -- Imports e.g. the use tactic
namespace mynat

-- Some set stuff
-- TODO: move to another file
section set_stuff
  variables T1 T2 : Type -- TODO: close the scope for t1 and t2?
  def injective {T1 T2} (f : T1 -> T2) : Prop := forall a b : T1, f a = f b -> a = b
  def surjective {T1 T2} (f : T1 -> T2) : Prop := forall b : T2, exists a : T1, f a = b
  def bijective {T1 T2} (f : T1 -> T2) : Prop := and (injective f) (surjective f)
  /- def subset t1 t2 := -/ 
  /- def proper_subset t1 t2 := -/
end set_stuff

-- Some logic stuff
section logic_stuff
/- open classical -/
  variable T : Type
  variable p : T -> Prop

  def not_exists_simp : not (exists t, p t) <-> forall t, not (p t) := 
  begin
    split,
      intro h,
      intro t,
      intro h_pt,
      exact h (exists.intro t h_pt),
  
      intro h,
      intro h_pt,
      exact (exists.elim h_pt) h,
  end

  -- TODO
  /- def not_forall_simp : (not (forall t, p t)) <-> (exists t, not (p t)) := sorry -/ 
end logic_stuff

--------------------------------------------------------------------------------


-- Axiom 2.1
axiom mynat : Type -- TODO: use something other than axiom here?
axiom zero : mynat

-- Axiom 2.2
axiom succ : mynat -> mynat
axiom succ_neq_0 : forall a : mynat, not (succ a = zero)
axiom succ_sur : forall a : mynat, not (a = zero) -> exists b : mynat, succ b = a -- succ is surjective onto mynat - zero, hence we can't just write succ_sur = surjective succ.
axiom succ_inj : injective succ


-- TODO: This is another approach?
/- def mynat_p := subtype (fun a : mynat, not (a = zero)) -- Positive naturals -/

-- Axiom 2.3
axiom induction {a : mynat} {p : mynat -> Prop} : p zero -> (p a -> p (succ a)) -> p a

-- Definition 2.1
def infinite (T : Type) : Prop :=
  exists f : T -> T,
  and
    (injective f)
    (not (surjective f))

example : infinite mynat :=
  begin
    use succ,
    split,
      exact succ_inj,

      dunfold surjective, -- dunfolds unfolds definitions :)
      intro h,
      exact exists.elim (h zero) succ_neq_0,
  end






/- -- TODO: With my current definition, I have to prove that add is a function -/
/- lemma add_is_well_defined {a b : mynat} : -/
/-   exists f : mynat -> mynat -> mynat, -/
/-   and -/
/-     (f a zero = a) -/
/-     (f a (succ b) = succ(f a b)) -/
/-   := sorry -/

-- It is interesting that, had we used the constructive definition
--  inductive mynat
--    | zero : mynat
--    | succ (n : mynat) : mynat
-- of the naturals, it would have been trivial to define addition as
--  def add : mynat -> mynat -> mynat
--    | a zero      := a
--    | a (succ b)  := succ (add a b)
-- But instead we have to spend some effort to prove (corollary 30) that addition is a function

end mynat
