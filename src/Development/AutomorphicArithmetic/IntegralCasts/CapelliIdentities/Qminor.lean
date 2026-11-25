module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuantumMinorsCasimir

@[expose] public section

namespace UpperTheory.Reformulated.B.Qf10

noncomputable def GlRel.{u_1} : {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop := fun {A} [Ring A] {n} E =>
  ∀ (a b c d : Fin n), E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - if d = a then E c b else 0

noncomputable def Tm.{u_1} : {A : Type u_1} → [inst : Ring A] → [Algebra ℂ A] → {n : ℕ} → (Fin n → Fin n → A) → ℂ → Fin n → Fin n → A := fun {A} [Ring A] [Algebra ℂ A] {n} E u a b => (if a = b then (algebraMap ℂ A) u else 0) + E a b

noncomputable def qminor.{u_1} : {A : Type u_1} →
  [inst : Ring A] → [Algebra ℂ A] → {n t : ℕ} → (Fin n → Fin n → A) → (Fin t → Fin n) → (Fin t → Fin n) → ℂ → A := fun {A} [Ring A] [Algebra ℂ A] {n t} E a b u =>
  ∑ σ, ↑↑(Equiv.Perm.sign σ) * (List.ofFn fun k => Tm E (u - ↑↑k) (a (σ k)) (b k)).prod

noncomputable def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E (id : Fin n → Fin n) id u

theorem casimir : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V]
  (E : Fin 2 → Fin 2 → Module.End ℂ V),
  GlRel E →
    ∀ (k : ℂ) (φ : V),
      (E 0 0) φ + (E 1 1) φ = 0 →
        (E 0 1) φ - (E 1 0) φ = (Complex.I * k) • φ →
          (E 0 0) φ - (E 1 1) φ = Complex.I • ((E 0 1) φ + (E 1 0) φ) →
            ∀ (u : ℂ),
              (qdet E (u + 1 / 2)) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  UpperTheory.Reformulated.B.QuantumMinorsCasimir.casimir

end UpperTheory.Reformulated.B.Qf10
