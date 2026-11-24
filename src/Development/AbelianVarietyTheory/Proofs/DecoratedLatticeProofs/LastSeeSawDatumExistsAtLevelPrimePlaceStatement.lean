module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeesawDatumEqLatticePairOverVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceAlongLineDatumOverVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuumStatement
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.LastSeeSawDatum (comb_apply' comb_smul_fun comb_sum_fun comb_swap vac_smul vac_sum) in

theorem _root_.GlobalTheory.T.lastSeeSawDatum_exists_at_levelPrimePlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  exact GlobalTheory.LastSeeSawDatum.lastDatum
