module

public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalHeisenbergEndomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelOppositeLagrangianUnitaryOp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalChartInertPlaceUnitaryPair
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilHomFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceWeilNormalisesHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesVacuumInertPlace
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem locDataV' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hTr : IsTriple B G X om om') {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : v ∉ X.T) : LocData G.M' om' v := by
  obtain ⟨ϖ, σL, q, δ, JS, JT, ψL, κ, ιS, ιT, hC⟩ := _root_.GlobalTheory.InertBridge.exists_chart F E σ B a a' G X om om' hTr v w hw hv
  have hC' := hC
  obtain ⟨unr, hodd, intS, intT, hS, hT, hδ, p1, p2, -, -, -, -, -, hιS, hιT, hKS, hKT⟩ := hC'
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.InertRho.exists_rho F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC
  obtain ⟨ω, hω⟩ := _root_.GlobalTheory.LocalWeilHom.local_weil_hom F E σ B a a' G X om om' hTr v w hw hv σL JS JT ιS ιT hιS hιT
  obtain ⟨r0, rmul⟩ := _root_.GlobalTheory.InertRhoLaw.rho_law F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨s, hs, hs0, hsv⟩ := _root_.GlobalTheory.InertBridgeVac.vac_locVac F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  have hline := _root_.GlobalTheory.InertBridgeLine.locVac_line F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s
  have hspan := _root_.GlobalTheory.InertSpan.span_translates_vac F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s hs
  have hnorm := GlobalTheory.T.inertPlace_weil_normalises_heisenberg F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ ω hω
  have hfix := _root_.GlobalTheory.InertBridge.fix_vac F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ω hω s hs
  refine ⟨w.adicCompletion E, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω,
    ιS, ιT, s, ⟨unr, hodd, intS, intT, hS, hT, hδ, p1, p2, r0, rmul, ?_, hnorm, ?_⟩, hs0, hsv, hspan, hs,
    hιS, hιT, hKS, hKT, fun g h m φ₁ hφ₁ => hω g h m φ₁ hφ₁⟩
  · rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono (by rintro _ ⟨x, rfl⟩; exact ⟨x, s, hsv, rfl⟩)
  · intro g h hg hh t ht
    obtain ⟨c, rfl⟩ := hline t hs ht
    rw [map_smul, hfix g h hg hh]

end PositivityTheory.Sph

end
