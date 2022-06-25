import tactic.interactive -- Imports e.g. the use tactic
import data.set
namespace mynat

-- Some set stuff
-- TODO: move to another file
section set_stuff
  variables T T1 T2 : Type -- TODO: close the scope for t1 and t2?
  def injective {T1 T2} (f : T1 -> T2) : Prop := forall a b : T1, f a = f b -> a = b
  def surjective {T1 T2} (f : T1 -> T2) : Prop := forall b : T2, exists a : T1, f a = b
  def bijective {T1 T2} (f : T1 -> T2) : Prop := and (injective f) (surjective f)

  -- TODO: What is the most natural way to do this? With or without the set library?
  /- def nonempty (T : Type) : Prop := exists (t : T), true -/
  /- def nonempty {T} (A : set T) : Prop := exists (t : T), t ∈ A -- or has_mem.mem t A -/
  /- def subset t1 t2 := -/ 
  /- def proper_subset t1 t2 := -/
  def Union {T} (A : set (set T)) : set T := {t : T | exists B ∈ A, t ∈ B} -- Union of collection of sets
  def Inter {T} (A : set (set T)) : set T := {t : T | forall B ∈ A, t ∈ B} -- Intersection of collection of sets

  -- TODO: this can be done much conciser
  def in_set_or_in_complement {T} {A : set T} : forall a : T, or (a ∈ A) (a ∈ Aᶜ) :=
    begin
      intro a,
      have h_n_ : a ∈ set.univ, exact (set.mem_univ a),
      rw (eq.symm $ set.union_compl_self A) at h_n_,
      rw (set.mem_union a A Aᶜ) at h_n_,
      exact h_n_,
    end
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

-- Axiom 2.3 -- TODO: which definition is easiest to work with?
/- axiom myinduction {p : mynat -> Prop} : p zero -> (forall a : mynat, p a -> p (succ a)) -> forall a : mynat, p a -/
axiom myinduction {A : set mynat} : zero ∈ A -> (forall n : mynat, n ∈ A -> succ n ∈ A) -> A = set.univ
-- named myinduction as not to nameclash with the builtin induction

-- Definition 2.1
def infinite (T : Type) : Prop :=
  exists f : T -> T,
  and
    (injective f)
    (not (surjective f))

-- Prove that the naturals are infinite
example : infinite mynat :=
  begin
    use succ,
    split,
      exact succ_inj,

      dunfold surjective, -- dunfolds unfolds definitions :)
      intro h,
      exact exists.elim (h zero) succ_neq_0,
  end

-- Definition 2.3
def final (A : set mynat) : Prop :=
  and
    (A.nonempty) -- mathlib docs: "The property s.nonempty expresses the fact that the set s is not empty. It should be used in theorem assumptions instead of ∃ x, x ∈ s or s ≠ ∅ as it gives access to a nice API thanks to the dot notation."
    (forall n : mynat, n ∈ A -> succ n ∈ A)

def initial (A : set mynat) : Prop :=
  final (compl A)

-- Proposition 12
section proposition_12
  variables A B I : set mynat

  -- TODO: state slightly more general versions of union_of_final_sets and intersection_of_initial_sets with arbitrary many sets?
  lemma union_of_final_sets : final A -> final B -> final (A ∪ B) :=
	begin
      dunfold final,

	  intro h_A,
      intro h_B,

      split,
        exact set.nonempty.inl h_A.left,

        intro n,
        intro h_n,
        rw set.mem_union,
        rw set.mem_union at h_n,
        cases h_n,
          exact or.inl (h_A.right n h_n),

          exact or.inr (h_B.right n h_n),
	end

  lemma intersection_of_initial_sets : initial A -> initial B -> initial (A ∩ B) :=
    begin
      dunfold initial,
      rw set.compl_inter,
      exact union_of_final_sets (compl A) (compl B),
    end

  -- Modified from the book. Added requirement that I is proper subset of naturals.
  lemma initial_iff_2 (I : set mynat) (h0 : set.nonempty Iᶜ) : initial I <-> forall n : mynat,
    or
      (n ∈ I)
      (not (succ n ∈ I)) :=
    begin
      unfold initial,
      unfold final,

      split,
        intro h_I,
        cases h_I with h_I1 h_I2,
        intro n,
          
        have h_n : or (n ∈ I) (n ∈ Iᶜ),
          exact in_set_or_in_complement n,

        cases h_n with h_n1 h_n2,
          left,
          exact h_n1,
            
          right,
          exact (h_I2 n) h_n2, -- Lean recognizes a ∉ A <-> a ∈ Aᶜ automatically


        intro h_I,
        split,
          exact h0,

          intro n,
          intro h_n,

          have h_n' : or (n ∈ I) (succ n ∉ I),
            exact h_I n,

          cases h_n' with h_n1 h_n2,
            exfalso,
            exact h_n h_n1,
            
            exact h_n2,
    end

  -- Lean recognizes a ∉ A is the same thing as a ∈ Aᶜ
  lemma initial_iff_3 (I : set mynat) (h0 : set.nonempty Iᶜ) : initial I <-> forall n : mynat, n ∉ I -> succ n ∉ I :=
    begin
      unfold initial,
      unfold final,
      
      split,
        intro h_I,
        cases h_I with h_I1 h_I2,
        intro n,
        intro h_n,

        exact h_I2 n h_n,

        intro h_I,
        split,
          exact h0,

          intro n,
          intro h_n,

          exact h_I n h_n,
    end

  lemma initial_iff_4 (I : set mynat) (h0 : set.nonempty Iᶜ) : initial I <-> forall n : mynat, succ n ∈ I -> n ∈ I :=
    begin
      unfold initial,
      unfold final,
      
      split,
        intro h_I,
        cases h_I with h_I1 h_I2,
        intro n,
        intro h_n1,

        have h_n2 : or (n ∈ I) (n ∈ Iᶜ),
          exact in_set_or_in_complement n,
        
        cases h_n2 with h_n2_l h_n2_r,
          exact h_n2_l,

          exfalso,
          exact (h_I2 n h_n2_r) h_n1,


        intro h_I,
        split,
          exact h0,

          intro n,
          intro h_n,

          have h_n2 : or (succ n ∈ I) (succ n ∈ Iᶜ),
            exact in_set_or_in_complement (succ n),

          cases h_n2 with h_n2_l h_n2_r,
            exfalso,
            exact h_n ((h_I n) h_n2_l),

            exact h_n2_r,
    end

  #check initial_iff_2
  #check initial_iff_3
  #check initial_iff_4
end proposition_12

-- Proposition 13
section proposition_13
  variables F I : set mynat

  lemma final_with_zero : zero ∈ F -> final F -> F = set.univ :=
    begin
      unfold final,

      intro h_F1,
      intro h_F2,
      cases h_F2 with h_F2_l h_F2_r, -- TODO: figure out how to throw out superfluous hypotheses, like h_F2_l?

      exact myinduction h_F1 h_F2_r,
    end

  lemma nonempty_initial : set.nonempty I -> initial I -> zero ∈ I :=
    begin
      unfold initial,
      unfold final,

      intro h_I1,
      intro h_I2,
      cases h_I2 with h_I2_l h_I2_r,

      have h_zero : or (zero ∈ I) (zero ∈ Iᶜ),
        exact in_set_or_in_complement zero,

      cases h_zero with h_zero_l h_zero_r,
        exact h_zero_l,

        exfalso,
        have h_I3 : Iᶜ = set.univ,
          exact myinduction h_zero_r h_I2_r,
        rw set.compl_univ_iff at h_I3,
        exact h_I1.ne_empty h_I3,
    end

  lemma initial_without_zero : initial I -> zero ∉ I -> I = ∅ :=
    begin
      intro h_I1,
      intro h_I2,

      have h_I3 : or (I = ∅) I.nonempty,
        exact set.eq_empty_or_nonempty I,

      cases h_I3 with h_I3_l h_I3_r,
        exact h_I3_l,

        exfalso,
        exact h_I2 (nonempty_initial_contains_zero I h_I3_r h_I1),
    end
  
  #check final_with_zero
  #check nonempty_initial
  #check initial_without_zero
end proposition_13

-- Definition 2.4
def plus (n : mynat) : set mynat := Inter {F | and (n ∈ F) (final F)}
/- def plus (n : mynat) : set mynat := {n : mynat | forall (F : set mynat), final F -> n ∈ F} -- Maybe this definition, though less verbatim, is easier to work with? -/
def minus (n : mynat) : set mynat := compl $ plus n

-- Proposition 14
section proposition_14
  theorem plus_zero : plus zero = set.univ :=
    begin
      unfold plus,
      unfold Inter,
      
      have h : forall (F : set mynat), (and (zero ∈ F) (final F)) -> (F = set.univ),
        unfold final,
        intro F,
        intro h_F,
  
        let prop_ : mynat -> Prop := (∈ F),
  
        let blergh := induction {(∈ F)} (h_F.left),
        
  
      /- rw set.mem_set_of, -/
  
    end
end proposition_14

#check in_set_or_in_complement
#check myinduction





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
