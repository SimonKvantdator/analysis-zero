import tactic.interactive -- Imports e.g. the use tactic
namespace mynat


-- Some set stuff
-- TODO: move to another file
variables T1 T2 : Type -- TODO: close the scope for t1 and t2?
def injective {T1 T2} (f : T1 -> T2) : Prop := forall a b : T1, f a = f b -> a = b
def surjective {T1 T2} (f : T1 -> T2) : Prop := forall b : T2, exists a : T1, f a = b
def bijective {T1 T2} (f : T1 -> T2) : Prop := and (injective f) (surjective f)
/- def subset t1 t2 := -/ 
/- def proper_subset t1 t2 := -/

-- Some logic stuff
variable T : Type
variable p : T -> Prop
def not_exists_simp : (not (exists x, p x)) <-> (forall x, not (p x)) := 
  begin
    split,
  end
def not_forall_simp : (not (forall x, p x)) <-> (exists x, not (p x)) := sorry

-- TODO: use something other than axiom here?

-- Axiom 2.1
axiom mynat : Type
axiom zero : mynat

-- Axiom 2.2
axiom succ : mynat -> mynat
axiom succ_neq_0 {a : mynat} : not (succ a = zero)
axiom succ_sur {a : mynat} : not (a = zero) -> exists b : mynat, succ b = a -- succ is surjective onto mynat - zero, hence we can't just write succ_sur = surjective succ.
axiom succ_inj : injective succ

/- -- TODO: This is another approach -/
/- def mynat_p := subtype (fun a : mynat, not (a = zero)) -- Positive naturals -/

-- Axiom 2.3
axiom induction {a : mynat} {p : mynat -> Prop} : p zero -> (p a -> p (succ a)) -> p a

-- Definition 2.1
-- TODO: write this function
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
      
  end


/- variable T : Type -/
/- variables a b : T -/
/- def bleh : exists f : T -> T, f a = f b := -/
/-   begin -/
/-     use fun (x : T), b, -/
/-   end -/








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
