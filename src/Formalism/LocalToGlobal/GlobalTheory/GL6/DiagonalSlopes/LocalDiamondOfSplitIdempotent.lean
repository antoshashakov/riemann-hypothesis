module

import Formalism.LocalToGlobal.GlobalTheory.GL6.AdmissibleOfSplitAndRoundTrips
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.ComplementSmulLocalExtensionMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open NumberField IsDedekindDomain Formalism.UG Classical Matrix Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Prime

theorem subgroup_prime_card_eq_top {G : Type} [AddCommGroup G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p)
    (H : AddSubgroup G) {y : G} (hy : y ∈ H) (hy0 : y ≠ 0) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.ne_zero)
  have hd : Nat.card H ∣ p := hG ▸ AddSubgroup.card_addSubgroup_dvd_card H
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exact absurd (AddSubgroup.mem_bot.1 ((AddSubgroup.eq_bot_of_card_eq H h) ▸ hy)) hy0
  · exact AddSubgroup.eq_top_of_card_eq H (h.trans hG.symm)

theorem idempotent_action_prime_card {O : Type} [Ring O] {G : Type} [AddCommGroup G] [Module O G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : O} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
      exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.idempotent_action_prime_card hp hG he

theorem unit_lift_int_prime_field {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime) (hK : Fintype.card K = p) (a : Kˣ) :
    ∃ k : ℤ, (k : K) = a ∧ ¬ (p : ℤ) ∣ k := by
  exact _root_.Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field hp hK a

end Prime

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem int_not_mem_prime_over (v : HeightOneSpectrum (𝓞 F)) {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} (hk : ¬ (T : ℤ) ∣ k) : (k : 𝓞 F) ∉ v.asIdeal := by
  exact _root_.Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.int_not_mem_prime_over v hT hv hk

theorem valuation_int_not_mem_eq_one (v : HeightOneSpectrum (𝓞 F)) {k : ℤ} (hk : (k : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (k : v.adicCompletion F) = 1 := by
  have h := v.valuedAdicCompletion_eq_valuation (K := F) (k : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hk] at h
  simpa using h

variable {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem scalar_mem_lattice_stabiliser {A : Type} [CommRing A] {S : Subring A} (Λ : Submodule S (Fin n → A))
    (g : GL (Fin n) A) (μ μ' : A) (hμ : μ ∈ S) (hμ' : μ' ∈ S) (h1 : μ' * μ = 1)
    (hg : ∀ x, (g : Matrix (Fin n) (Fin n) A) *ᵥ x = μ • x) : g ∈ stabGL Λ := by
  intro x
  rw [hg]
  constructor
  · intro hx
    exact Λ.smul_mem (⟨μ, hμ⟩ : S) hx
  · intro hx
    have h := Λ.smul_mem (⟨μ', hμ'⟩ : S) hx
    change μ' • μ • x ∈ Λ at h
    rwa [smul_smul, h1, one_smul] at h

theorem local_diamond_of_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (c c' e : E ⊗[F] v.adicCompletion F)
    (hc : c ∈ intV E v) (hc' : c' ∈ intV E v) (he : e ∈ intV E v) (hee : e * e = e)
    (hσ : sigR σ (v.adicCompletion F) e = 1 - e) (hσc : sigR σ (v.adicCompletion F) c = c)
    (hσc' : sigR σ (v.adicCompletion F) c' = c') (hcc : c * c' = 1)
    (hkc : (k : E ⊗[F] v.adicCompletion F) * c = 1)
    (hact : ∀ y : S.fM v hv, (⟨e, he⟩ : intV E v) • y = y) : IsLocalDiamond S v hv k := by
  exact _root_.Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_idempotent S v hv
    k c c' e hc hc' he hee hσ hσc hσc' hcc hkc hact

theorem local_diamond_of_split_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hT : T.Prime) (k : ℤ) (hk : ¬ (T : ℤ) ∣ k) (e : E ⊗[F] v.adicCompletion F)
    (he : e ∈ intV E v) (hee : e * e = e) (hσ : sigR σ (v.adicCompletion F) e = 1 - e) : IsLocalDiamond S v hv k := by
  apply Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent <;> assumption

end Local

section Tied

variable {D : D7} {u : D.what₂.Word}

def SplitAtT (A : AtTTied u) : Prop :=
  ∀ v : (D.mem u).A.vT, ∃ e ∈ intV D.host.E (A.eV v).1, e * e = e ∧
    sigR (sigD D) ((A.eV v).1.adicCompletion D.host.F) e = 1 - e

theorem local_diamonds_of_split (Tf : Forms0 D u) (hs : SplitAtT Tf.atT) : LocalDiamondElementsExist Tf := by
  intro i hi h0 v a
  obtain ⟨k, hk, hkT⟩ := unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := hs v
  exact ⟨k, hk, local_diamond_of_split_idempotent (Tf.cls i hi h0).lev _ _ (D.mem u).A.T_prime k hkT e he hee hσ⟩

theorem diamond_elements_of_split (Tf : Forms0 D u) (hs : SplitAtT Tf.atT) : DiamondElementsExist Tf :=
  diamond_elements_of_local Tf (local_diamonds_of_split Tf hs)

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
