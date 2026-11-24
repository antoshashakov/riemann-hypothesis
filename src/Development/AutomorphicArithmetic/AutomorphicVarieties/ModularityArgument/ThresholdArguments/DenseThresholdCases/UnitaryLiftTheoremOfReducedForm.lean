module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
public import Formalism.SharedLemmas.TotDiscQuot

@[expose] public section




section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  first
  | exact _root_.Formalism.SharedLemmas.totDisc_quot
  | (apply _root_.Formalism.SharedLemmas.totDisc_quot <;> assumption)
theorem UpperTheory.V.UnitaryThreeInertia.unitary_lift_of_reduced_core :
    _root_.UpperTheory.V.Aut.ThmS6Core_s → _root_.UpperTheory.V.Aut.ThmS6_s := by
  intro h K _ _ _ hK Ω _ _ _ l _ ι c N _ e ψ o₁ hd S A F hF
  obtain ⟨g₁, hg, H⟩ := h K hK Ω l ι c N e ψ o₁ hd S A F hF
  refine ⟨g₁, hg, fun R _ _ _ u hu => ⟨(H R u hu).1, fun ξ r h1 h2 => ?_⟩⟩
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : CompactSpace (Gam Ω S) := inferInstance
  haveI : T2Space (Gam Ω S) := inferInstance
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  have hOk := hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hz : F.IsCharZeroPt g₁ r := isCharZeroPt_of_isPtHom (l := l) F hOk g₁ hg u hu (H R u hu).1 ξ r h1
  exact ⟨matIrr_open Ω c e ψ o₁ hd S A F hF g₁ hg r hz h2, matIrr_cyc Ω c e ψ o₁ hd S A F hF g₁ hg r hz h2,
    (H R u hu).2 ξ r h1 h2⟩
end
