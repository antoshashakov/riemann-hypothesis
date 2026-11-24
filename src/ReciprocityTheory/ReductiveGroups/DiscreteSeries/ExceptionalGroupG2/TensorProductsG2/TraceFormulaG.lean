module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import Std.Tactic.BVDecide.Normalize.Prop
import Supplements.Analysis.TensorTraceClosure

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem tfg_gen {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (S : Submodule ℂ (Fin n → M))
    (hV : tensSub V ≤ S) (hS : ∀ a b, ∀ f ∈ S, tensF dual E a b f ∈ S) : tensSub (genSub E V) ≤ S := by
  apply ReciprocityTheory.ChartRestriction.DS.tfg_gen <;> assumption

theorem tfg_real {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ X} (hU : IsInfUnitary ε E) {c : ℂ} {v : X}
    (h : casimir E v = c • v) : casimir E v = ((c.re : ℝ) : ℂ) • v := by
  apply ReciprocityTheory.ChartRestriction.DS.tfg_real <;> assumption

theorem tf_closure_stable (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {y : D} (hy : y ∈ genSub E V) :
    ∀ g ∈ UJset ε, ∀ v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure,
      tfRdiag ε g v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure := by
  have hclosure :=
    ReciprocityTheory.ChartRestriction.DS.SharedTraceClosure.tf_closure_stable_of_memLp
      dual hσ hD hsm hV hc hW hP hEP hy
  let S := Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
    v = WithLp.toLp 2 (fun c => toL2 ε (fun g => coefMap dual σ
      (Pi.single c (tfSgn ε c • (y : H))) (fun d => ((P f d : D) : H)) g))}
  change ∀ g ∈ UJset ε, ∀ v ∈ S.topologicalClosure,
    tfRdiag ε g v ∈ S.topologicalClosure at hclosure ⊢
  simp only [S, coefMap] at hclosure ⊢
  exact hclosure

end ReciprocityTheory.ChartRestriction.DS.G2
