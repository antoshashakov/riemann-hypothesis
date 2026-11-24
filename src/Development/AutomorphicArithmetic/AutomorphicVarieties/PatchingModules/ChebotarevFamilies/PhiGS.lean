module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Formalism.SharedLemmas.PhiCondFiniteH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem core_lemma {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H K : Subgroup Γ)
    [Finite (Γ ⧸ H)] (hK : IsOpen (K : Set Γ)) (hKH : K ≤ H) :
    ∃ U : Set Γ, IsOpen U ∧ (1 : Γ) ∈ U ∧ ∀ k ∈ U, ∀ y : Γ ⧸ H, (y.out)⁻¹ * k * y.out ∈ K ∧ k • y = y := by
  refine ⟨⋂ y : Γ ⧸ H, (fun k => (y.out)⁻¹ * k * y.out) ⁻¹' (K : Set Γ), ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun y =>
      hK.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · simp
  · intro k hk y
    have hy : (y.out)⁻¹ * k * y.out ∈ K := Set.mem_iInter.mp hk y
    refine ⟨hy, ?_⟩
    rw [← QuotientGroup.out_eq' y, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    have hi := H.inv_mem (hKH hy)
    simpa [mul_assoc] using hi

private theorem mult_map_mul_right_eq_of_chi_eq_one {Γ : Type} [Group Γ] (H : Subgroup Γ) (g g' : Γ) (x : Γ ⧸ H)
    (h : (g⁻¹ * g') • (g⁻¹ • x) = g⁻¹ • x) : g'⁻¹ • x = g⁻¹ • x := by
  calc g'⁻¹ • x = (g⁻¹ * g')⁻¹ • (g⁻¹ • x) := by
        rw [← mul_smul]
        congr 1
        group
    _ = g⁻¹ • x := by rw [inv_smul_eq_iff, h]

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  exact Formalism.SharedLemmas.phiCond_of_finite_H1 n h

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.phiGS :
    GlobalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev), PhiCond V.frame.Γ l := by
  intro hGF l _ L Ω _ _ _ _ _ _ s V
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Plc (Lp L)), (S : Set (Plc (Lp L))) = V.S' :=
    ⟨V.fin.toFinset, V.fin.coe_toFinset⟩
  show PhiCond (ReciprocityTheory.Gal.GS Ω V.S') l
  rw [← hS]
  have key : PhiCond (ReciprocityTheory.Gal.GS Ω (S : Set (Plc (Lp L)))) (l ^ 1) := by
    apply phi_condition_of_finite_cohomology
    intro M _ _ _ _ _ ρ hρ
    have habove : ReciprocityTheory.Gal.ContainsAbove S l := by
      intro v hv
      have hv' : v ∈ V.S' := V.sub (Or.inl hv)
      rw [← hS] at hv'
      exact_mod_cast hv'
    exact (hGF (Lp L) Ω l 1 M S ρ one_pos habove hρ).2.1
  rw [pow_one] at key
  exact key
