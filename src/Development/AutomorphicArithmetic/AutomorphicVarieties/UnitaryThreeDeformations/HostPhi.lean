module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
public import Formalism.SharedLemmas.PhiCondFiniteH1
public import Formalism.SharedLemmas.TotDiscQuot

@[expose] public section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  first
  | exact _root_.Formalism.SharedLemmas.totDisc_quot
  | (apply _root_.Formalism.SharedLemmas.totDisc_quot <;> assumption)

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  exact Formalism.SharedLemmas.phiCond_of_finite_H1 n h

theorem UpperTheory.V.UnitaryThreeInertia.hostFrame_phi :
    GlobalFiniteness → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    PhiCond (Gam Ω S) l ∧ CompactSpace (Gam Ω S) ∧ T2Space (Gam Ω S) ∧ TotallyDisconnectedSpace (Gam Ω S) ∧ CompactSpace (Formalism.ConjugateSelfDual.G ℚ Ω) ∧ T2Space (Formalism.ConjugateSelfDual.G ℚ Ω) ∧ TotallyDisconnectedSpace (Formalism.ConjugateSelfDual.G ℚ Ω) := by
  intro hGF Ω _ _ _ l _ c N _ e ψ o₁ _hD S A F hF
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hT2 : T2Space (Gam Ω S) := by
    haveI : IsClosed (NS Ω (↑S : Set Pl) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := isClosed_NS (F := ℚ) Ω _
    unfold Gam
    infer_instance
  have hTD : TotallyDisconnectedSpace (Gam Ω S) := by
    unfold Gam
    exact totDisc_quot _ (isClosed_NS (F := ℚ) Ω _)
  have hCA : ReciprocityTheory.Gal.ContainsAbove (F := ℚ) S l := by
    unfold ReciprocityTheory.Gal.ContainsAbove
    intro v hv
    apply (hF.mem v).mpr
    simpa [Nat.cast_mul, mul_comm] using Ideal.mul_mem_right (N : NumberField.RingOfIntegers ℚ) v.asIdeal hv
  unfold GlobalFiniteness at hGF
  have key : ∀ k : ℕ, k = l ^ 1 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod k) M] [TopologicalSpace M]
      [DiscreteTopology M] [Finite M] (ρ : Representation (ZMod k) (Gam Ω S) M),
      ReciprocityTheory.Gal.ContAction ρ → Finite (H1 ρ) := by
    intro k hk
    subst hk
    intro M _ _ _ _ _ ρ hρ
    have hGFa := hGF ℚ Ω l 1 M S ρ
    unfold ReciprocityTheory.Gal.GlobalFinitenessAt at hGFa
    exact (hGFa Nat.one_pos hCA hρ).2.1
  have hPhi : PhiCond (Gam Ω S) l := by
    apply phi_condition_of_finite_cohomology l
    intro M _ _ _ _ _ ρ hρ
    exact key l (pow_one l).symm M ρ hρ
  exact ⟨hPhi, inferInstance, hT2, hTD, inferInstance, inferInstance, inferInstance⟩
