import tactic.interactive -- Imports e.g. the use tactic
import data.set
namespace mynat

-- Some set stuff
-- TODO: move to another file?
section set_stuff -- {{{
  variables T T1 T2 : Type -- TODO: close the scope for t1 and t2?
  def injective {T1 T2} (f : T1 -> T2) : Prop := forall a b : T1, f a = f b -> a = b -- Can be used interchangably with function.injective from core.

  def surjective {T1 T2} (f : T1 -> T2) : Prop := forall b : T2, exists a : T1, f a = b
  def bijective {T1 T2} (f : T1 -> T2) : Prop := and (injective f) (surjective f)

  -- TODO: What is the most natural way to do this? With or without the set library?
  /- def nonempty (T : Type) : Prop := exists (t : T), true -/
  /- def nonempty {T} (A : set T) : Prop := exists (t : T), t ∈ A -- or has_mem.mem t A -/
  /- def subset t1 t2 := -/ 
  /- def proper_subset t1 t2 := -/
  def Union {T} (AA : set (set T)) : set T := {t : T | exists A ∈ AA, t ∈ A} -- Union of collection of sets
  def Inter {T} (AA : set (set T)) : set T := {t : T | forall A ∈ AA, t ∈ A} -- Intersection of collection of sets

  /- def inter_distributive {T} (p : set T -> Prop) := forall A B : set T, p A ∧ p B -> p (A ∩ B) -/
  /- def Inter_distributive {T} (p : set T -> Prop) := forall AA : set (set T), (forall A ∈ AA, p A) -> p (Inter AA) -/
  /- /1- lemma inductive_inter_distributive {T} (p : set T -> Prop) : inter_distributive p -> Inter_distributive p -1/ -- TODO: needs to be countable? -/

  -- TODO: this can be done much conciser?
  def in_set_or_in_complement {T} {A : set T} : forall a : T, or (a ∈ A) (a ∈ Aᶜ) :=
    begin
      intro a,
      have h_n_ : a ∈ set.univ, exact (set.mem_univ a),
      rw (eq.symm $ set.union_compl_self A) at h_n_,
      rw (set.mem_union a A Aᶜ) at h_n_,
      exact h_n_,
    end
end set_stuff -- }}}

-- Some logic stuff
section logic_stuff -- {{{
/- open classical -/
  variable T : Type
  variable p : T -> Prop

  def not_exists_simp : not (exists t, p t) <-> forall t, not (p t) := /- {{{ -/
  begin
    split,
      intro h,
      intro t,
      intro h_pt,
      exact h (exists.intro t h_pt),
  
      intro h,
      intro h_pt,
      exact (exists.elim h_pt) h,
  end/- }}} -/

    lemma contrapositive {A B : Prop} : (A <-> B) -> (not A <-> not B) :=/- {{{ -/
      begin
        intro h_AB,
        split,
          intro h_nA,
          intro h_B,
          have h_A : A := h_AB.elim_right h_B,
          exact h_nA h_A,

          intro h_nB,
          intro h_A,
          have h_B : B := h_AB.elim_left h_A,
          exact h_nB h_B,
      end/- }}} -/

  -- TODO
  /- def not_forall_simp : (not (forall t, p t)) <-> (exists t, not (p t)) := sorry -/ 
end logic_stuff -- }}}

--------------------------------------------------------------------------------

-- Axioms for the naturals
-- Axiom 2.1 {{{
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
-- }}}

-- Infinite sets
-- Definition 2.1 {{{
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
-- }}}

-- Initial and Final subsets of the naturals
-- Definition 2.3 {{{
def final (A : set mynat) : Prop :=
  and
    (A.nonempty) -- mathlib docs: "The property s.nonempty expresses the fact that the set s is not empty. It should be used in theorem assumptions instead of ∃ x, x ∈ s or s ≠ ∅ as it gives access to a nice API thanks to the dot notation."
    (forall n : mynat, n ∈ A -> succ n ∈ A)

def initial (A : set mynat) : Prop :=
  final (compl A)
-- }}}

-- Proposition 12
section proposition_12 -- {{{
  variables A B: set mynat

  -- TODO: state slightly more general versions of union_of_final_sets and intersection_of_initial_sets with arbitrary many sets?
  lemma union_of_final_sets : final A -> final B -> final (A ∪ B) := -- {{{
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
	end -- }}}

  lemma intersection_of_initial_sets : initial A -> initial B -> initial (A ∩ B) := -- {{{
    begin
      dunfold initial,
      rw set.compl_inter,
      exact union_of_final_sets (compl A) (compl B),
    end -- }}}

  -- Modified from the book. Added requirement that I is proper subset of naturals.
  lemma initial_iff_cond2 (I : set mynat) (h0 : set.nonempty Iᶜ) : initial I <-> forall n : mynat, --{{{
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
    end -- }}}

  lemma initial_iff_cond3 (I : set mynat) (h0 : set.nonempty Iᶜ) : initial I <-> forall n : mynat, n ∉ I -> succ n ∉ I := -- {{{
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
      -- Lean recognizes a ∉ A is the same thing as a ∈ Aᶜ
    end -- }}}

  lemma initial_iff_cond4 (I : set mynat) (h0 : set.nonempty Iᶜ) : initial I <-> forall n : mynat, succ n ∈ I -> n ∈ I := -- {{{
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
    end -- }}}

    theorem succ_final (F : set mynat) (h0 : final F) : final (succ '' F) := -- {{{
      begin
        unfold final,
        unfold final at h0,
        split,
          exact set.nonempty.image succ h0.elim_left,

          have h0 : ∀ (n : mynat), n ∈ F -> succ n ∈ F := h0.elim_right,

          intro n,
          intro h_n,

          unfold set.image,
          unfold set.image at h_n,

          rw set.mem_set_of,
          rw set.mem_set_of at h_n,

          cases h_n with l h_n,
          use succ l,
          have apply_succ : forall (a b : mynat), a = b -> succ a = succ b, cc, -- TODO: there must be some standard way to do this.
          exact and.intro (h0 l h_n.elim_left) (apply_succ (succ l) n h_n.elim_right),
      end -- }}}

  #check initial_iff_cond2
  #check initial_iff_cond3
  #check initial_iff_cond4
end proposition_12 -- }}}

-- Proposition 13
section proposition_13 -- {{{
  variables F I : set mynat

  lemma final_with_zero : zero ∈ F -> final F -> F = set.univ := -- {{{
    begin
      unfold final,

      intro h_F1,
      intro h_F2,
      cases h_F2 with h_F2_l h_F2_r, -- TODO: figure out how to throw out superfluous hypotheses, like h_F2_l?

      exact myinduction h_F1 h_F2_r,
    end -- }}}

  lemma nonempty_initial : set.nonempty I -> initial I -> zero ∈ I := -- {{{
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
    end -- }}}

  lemma initial_without_zero : initial I -> zero ∉ I -> I = ∅ := -- {{{
    begin
      intro h_I1,
      intro h_I2,

      have h_I3 : or (I = ∅) I.nonempty,
        exact set.eq_empty_or_nonempty I,

      cases h_I3 with h_I3_l h_I3_r,
        exact h_I3_l,

        exfalso,
        exact h_I2 (nonempty_initial I h_I3_r h_I1),
    end -- }}}
  
  #check final_with_zero
  #check nonempty_initial
  #check initial_without_zero
end proposition_13 -- }}}

-- The initial and final sets generated by a natural
-- Definition 2.4 {{{
def plus (n : mynat) : set mynat :=
  Inter {F | and (n ∈ F) (final F)}
def minus (n : mynat) : set mynat :=
  compl $ plus n

-- Used in proposition 16
lemma plus_subset_final : forall (F : set mynat) (n ∈ F), final F -> plus n ⊆ F := -- {{{
  begin
    intro F,
    intro n,
    intro h_n,
    intro h_F1,

    unfold plus,
    unfold Inter,
    rw set.subset_def,

    intro t,
    rw set.mem_set_of,
    intro h_F2,
    let h_F2 := h_F2 F,
    rw set.mem_set_of at h_F2,

    exact h_F2 (and.intro h_n h_F1),
  end -- }}}
-- }}}

-- Proposition 14
section proposition_14 -- {{{
  theorem plus_zero : plus zero = set.univ := -- {{{
    begin
      unfold plus,
      unfold Inter,

      rw set.eq_univ_iff_forall,
      intro n,
      rw set.mem_set_of,
      intro B,
      rw set.mem_set_of,
      intro h_B,
      cases h_B with h_B_left h_B_right,

      have h_B1 : B = set.univ,
        exact final_with_zero B h_B_left h_B_right,
      exact set.eq_univ_iff_forall.elim_left h_B1 n,
    end -- }}}

  theorem minus_zero : minus zero = ∅ := -- {{{
    begin
      unfold minus,
      exact set.compl_empty_iff.elim_right plus_zero,
    end -- }}}
end proposition_14 -- }}}

-- Proposition 15
section proposition_15 -- {{{
  variable n : mynat

  theorem n_in_plus_n : n ∈ plus n := -- {{{
  begin
    unfold plus,
    unfold Inter,

    rw set.mem_set_of,
    intro B,
    rw set.mem_set_of,
    cc,
  end -- }}}

  theorem n_notin_plus_n : n ∉ minus n :=/- {{{ -/
    set.not_mem_compl_iff.elim_right (n_in_plus_n n)/- }}} -/

  theorem plus_final : final (plus n) := -- {{{
    begin
      unfold final,
      split,
        have h_n : n ∈ plus n,
          unfold plus,
          unfold Inter,
          rw set.mem_set_of,
          intro B,
          rw set.mem_set_of,
          cc,

        exact set.nonempty_of_mem h_n,
        intro m,
        intro h_m,
        unfold plus,
        unfold plus at h_m,
        unfold Inter,
        unfold Inter at h_m,
        rw set.mem_set_of,
        rw set.mem_set_of at h_m,

        intro B,
        have h_m := h_m B,
        rw set.mem_set_of,
        rw set.mem_set_of at h_m,

        intro h_B,
        have h_m : m ∈ B := h_m h_B,
        have h_B : final B := h_B.elim_right,
        exact (h_B.right m) h_m,
    end -- }}}

  theorem plus_union_minus : (plus n) ∪ (minus n) = set.univ := -- {{{
    begin
      unfold minus,
      exact set.union_compl_self (plus n),
    end -- }}}
end proposition_15 -- }}}

-- Proposition 16
section proposition_16 -- {{{
  variable n : mynat

  lemma final_n_union_psn : final ({n} ∪ plus (succ n)) := -- {{{
    begin
      have h_psn : final (plus (succ n))
        := plus_final (succ n),

      unfold final,
      split,
        exact set.nonempty.inl (set.singleton_nonempty n),
  
        intro l,
        intro h_l,
        cases h_l,
          have h_l : l = n
            := set.mem_singleton_iff.elim_left h_l,
          rw h_l,
          have h_succ_n : succ n ∈ plus (succ n)
            := (n_in_plus_n (succ n)),
          exact set.mem_union_right {n} h_succ_n,
  
          exact set.mem_union_right {n} (h_psn.elim_right l h_l),
    end -- }}}

  theorem plus_succ : plus (succ n) = succ '' (plus n) := -- {{{
    begin
      let lhs := plus (succ n),
      let rhs := succ '' (plus n),
      have h_lhs : final lhs
        := plus_final (succ n),

      have h1 : lhs ⊆ rhs,/- {{{ -/
        have h_spn : final rhs
          := succ_final (plus n) (plus_final n),
        have h_succ_n : succ n ∈ rhs
          := set.mem_image_of_mem succ (n_in_plus_n n),
        exact plus_subset_final rhs (succ n) h_succ_n h_spn,/- }}} -/

      have h2 : rhs ⊆ lhs,/- {{{ -/
        rw set.subset_def,
        intro m,
        intro h_m,

        have h_r : ∃ (x : mynat), x ∈ plus n ∧ succ x = m
          := (set.mem_image succ (plus n) m).elim_left h_m,
        cases h_r with r h_r,
        cases h_r with h_r_left h_r_right,

        let F1 := lhs ∪ {n},
        have h_F1 : final (lhs ∪ {n}), -- TODO: Why can't I just write final F1 here?
          rw set.union_comm lhs {n},
          exact final_n_union_psn n,

        have h_n : n ∈ F1
          := set.mem_union_right lhs (set.mem_singleton n),

        have h_pn : plus n ⊆ F1
          := plus_subset_final F1 n h_n h_F1,
        have h_r_left : r ∈ F1
          := h_pn h_r_left,

        have h_r : r ∈ lhs ∨ r = n
          := (set.mem_union r lhs {n}).elim_left h_r_left,

        cases h_r,
          rw eq.symm h_r_right,
          exact h_lhs.elim_right r h_r,

          rw eq.symm h_r_right,
          rw h_r,
          exact n_in_plus_n (succ n),/- }}} -/
          
      exact set.eq_of_subset_of_subset h1 h2,
    end -- }}}

  theorem plus_n_as_union : plus n = {n} ∪ plus (succ n) :=/- {{{ -/
    begin
      let lhs := plus n,
      let rhs := {n} ∪ plus (succ n),

      have h1 : lhs ⊆ rhs,/- {{{ -/
        begin
          have h_n : n ∈ rhs,
            simp,

          have h_rhs : final rhs,
            exact final_n_union_psn n,

          exact plus_subset_final rhs n h_n h_rhs,
        end,/- }}} -/

      have h2 : rhs ⊆ lhs,/- {{{ -/
        begin
          simp,
          split,
            exact n_in_plus_n n,

            have h_final : forall (n_ : mynat) (F : set mynat), n_ ∈ F -> final F -> plus (succ n_) ⊆ F,
              intro n_,
              intro F,
              intro h_n_,
              intro h_F,
              rw plus_succ,
              intro m,

              unfold set.image, simp,
              intro r,
              intros h_r1 h_r2,
              have h_r1 : r ∈ F,
                apply plus_subset_final F n_ h_n_ h_F,
                exact h_r1,

              rw eq.symm h_r2,
              exact h_F.elim_right r h_r1,

            exact h_final n lhs (n_in_plus_n n) (plus_final n),
        end,/- }}} -/

      exact set.eq_of_subset_of_subset h1 h2,
    end/- }}} -/

    theorem n_not_in_plus_succ_n : n ∉ plus (succ n) :=/- {{{ -/
      begin
        let I := {a : mynat | a ∉ plus (succ a)},
        have h_I : I = set.univ,
          apply myinduction,

          simp,
          rw plus_succ zero,
          unfold set.image, simp,
          exact fun b, fun _, succ_neq_0 b,

          simp,
          intro n,
          intro h_n,
          rw plus_succ,
          rw eq.symm (set.mem_compl_eq (succ '' plus (succ n)) (succ n)),
          rw eq.symm (set.mem_compl_eq (plus (succ n)) n) at h_n,
          apply set.image_compl_subset succ_inj,
          exact (function.injective.mem_set_image succ_inj).elim_right h_n,

        /- simp only [I] at h_n, -- unfold I -/
        have h_n : n ∈ I,
          begin
            rw h_I,
            exact set.mem_univ n,
          end,
        simp at h_n,
        exact h_n,
      end/- }}} -/
    
  #check plus_succ
  #check plus_n_as_union
  #check n_notin_plus_n
end proposition_16 -- }}}

-- Corollary 17
section corollary_17 -- {{{
  variable n : mynat

  theorem minus_succ_n_as_union : minus (succ n) = {n} ∪ (minus n) :=
    begin
      unfold minus,
      have h1 := eq.symm (plus_n_as_union n),
      apply_fun compl at h1,
      rw set.compl_union _ _ at h1,
      apply_fun (∪) {n} at h1,
      rw set.union_distrib_left _ _ _ at h1,
      rw set.union_compl_self _ at h1,
      rw set.univ_inter at h1,

      have h2 := n_not_in_plus_succ_n n,
      rw eq.symm (set.mem_compl_eq _ _) at h2,
      rw iff.symm set.singleton_subset_iff at h2,
      rw set.union_eq_right_iff_subset.elim_right h2 at h1,
      assumption,
    end
end corollary_17 -- }}}

-- Proposition 18
section proposition_18
  variables m n : mynat

  theorem final_subset_or_superset_of_plus_n {F : set mynat} : (final F) -> (F ⊆ plus n) ∨ (plus n ⊆ F) :=/- {{{ -/
    begin
      intro h_F,
      let A := {p : mynat | F ⊆ plus p ∨ plus p ⊆ F },
      have h_A : A = set.univ,
        apply myinduction,

        simp,
        rw plus_zero,
        simp,

        intro p,
        intro h_p,
        cases h_p with h_p1 h_p2,
          simp,
          rw plus_n_as_union p at h_p1,
          cases @in_set_or_in_complement mynat F p with h_p3 h_p4,
            right, -- From here, we see that F = plus p, so we can start expanding definitions
            unfold plus,
            unfold Inter,
            intro t, simp,
            intro h_t,
            have h_p5 : succ p ∈ F := h_F.elim_right p h_p3,
            exact h_t F h_p5 h_F,

            left,
            rw iff.symm set.singleton_subset_iff at h_p4,
            rw set.subset_compl_comm at h_p4,
            have h_p5 := set.inter_subset_inter h_p1 h_p4,
            rw set.inter_distrib_right at h_p5,
            simp at h_p5,
            exact h_p5.left,

          simp,
          right,
          rw plus_n_as_union at h_p2,
          rw set.union_subset_iff at h_p2,
          exact h_p2.right,

          have h_n : n ∈ A,
            begin
              rw h_A,
              exact set.mem_univ n,
            end,
          simp at h_n,
          exact h_n,
    end/- }}} -/

  theorem initial_subset_or_superset_of_minus_n {I : set mynat} : (initial I) -> (I ⊆ minus n) ∨ (minus n ⊆ I) :=/- {{{ -/
    begin
      sorry,
    end/- }}} -/

  theorem plus_n_subset_or_superset_of_plus_m  : (plus n ⊆ plus m) ∨ (plus m ⊆ plus n) :=/- {{{ -/
    begin
      sorry,
    end
end proposition_18/- }}} -/


variable a : mynat

#check in_set_or_in_complement
#check plus_zero
#check (∪)
#check (∩)
#check compl
#check funext
#check function.injective.mem_set_image
#check succ_inj
#print injective


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
