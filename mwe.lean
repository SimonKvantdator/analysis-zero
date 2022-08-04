import data.set
import data.set.function

axiom mynat : Type
axiom zero : mynat
axiom succ : mynat -> mynat
axiom succ_neq_0 {a : mynat} : not (succ a = zero)
axiom succ_sur {a : mynat} : not (a = zero) -> exists b : mynat, succ b = a
axiom succ_inj : function.injective succ
axiom myinduction {A : set mynat} : zero ∈ A -> (forall n : mynat, n ∈ A -> succ n ∈ A) -> A = set.univ

def Inter {T} (AA : set (set T)) : set T := {t : T | forall A ∈ AA, t ∈ A}
def final (A : set mynat) : Prop :=
  and
    (A.nonempty)
    (forall n : mynat, n ∈ A -> succ n ∈ A)
def plus (n : mynat) : set mynat :=
  Inter {F | and (n ∈ F) (final F)}
def minus (n : mynat) : set mynat :=
  compl $ plus n

def leq (m n : mynat) : Prop := minus m ⊆ minus n
infix `≤`:80 := leq 

lemma leq_zero {n : mynat} : (n ≤ zero) <-> n = zero :=
begin sorry, end

lemma minus_zero : minus zero = ∅ :=
begin sorry, end

variables {AA : Type} {A : set AA}
variable {n : mynat}

theorem inductive_definitions_general
  (g : (Σ n : mynat, minus n -> A) -> A) :
  ∃! (f : mynat -> A),
    forall m : mynat,
      f m = g ⟨m, (minus m).restrict f⟩
  :=
begin
  apply exists_unique_of_exists_of_unique,

    let I := {n : mynat | exists (h : mynat -> A), forall m ≤ n, h m = g ⟨m, (minus m).restrict h⟩},
    have h_I : I = set.univ,
    apply myinduction,
      simp,

      have h_ : mynat -> A, sorry,
      simp [leq_zero],
      use (fun _, g ⟨zero, (minus zero).restrict h_⟩),
      rw minus_zero,

end
