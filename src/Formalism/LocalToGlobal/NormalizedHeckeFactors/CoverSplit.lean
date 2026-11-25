module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Automorphisms.InstMainA
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2

variable {D : D7}

local notation "cO" => IsCMField.ringOfIntegersComplexConj D.host.E

theorem cO_cO (x : 𝓞 D.host.E) : cO (cO x) = x := by
  apply RingOfIntegers.ext
  rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
  exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)

theorem cO_algebraMap (a : 𝓞 (maximalRealSubfield D.host.E)) :
    cO (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a) =
      algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩

def conjPlE (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
    · show (cO : 𝓞 D.host.E →+* 𝓞 D.host.E) (cO y) ∈ P.asIdeal
      rw [RingHom.coe_coe, cO_cO]; exact hy
    · intro h0
      apply hy0
      rw [← cO_cO y, h0, map_zero]

theorem mem_conjPlE (P : PlE D.host) (x : 𝓞 D.host.E) : x ∈ (conjPlE P).asIdeal ↔ cO x ∈ P.asIdeal := Iff.rfl

theorem eq_or_eq_conjPlE (P w : PlE D.host)
    (hw : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) :
    w = P ∨ w = conjPlE P := by
  apply GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE <;> assumption

def conjSplit (s : SplitPlace D.host.E) : SplitPlace D.host.E :=
  ⟨s.v, s.i.comp (IsCMField.complexConj D.host.E).toAlgHom⟩

theorem mem_conj_w (s : SplitPlace D.host.E) (x : 𝓞 D.host.E) : x ∈ (conjSplit s).w.asIdeal ↔ cO x ∈ s.w.asIdeal := by
  show Valued.v ((conjSplit s).i (x : D.host.E)) < 1 ↔ Valued.v (s.i ((cO x : 𝓞 D.host.E) : D.host.E)) < 1
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  rfl

theorem splitEx_of (hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x)
    (hsplit : ∀ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)),
      (∃ w w' : PlE D.host, w ≠ w' ∧
        w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v₀.asIdeal ∧
        w'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v₀.asIdeal) →
      ∃ s : SplitPlace D.host.E, s.v = v₀) :
    SplitEx D := by
  exact _root_.GlobalTheory.SplitConjPlace.splitEx_of hstar hsplit

end Formalism.L2

namespace Formalism.L2

variable {D : D7}

local notation "cO" => IsCMField.ringOfIntegersComplexConj D.host.E
local notation "Fp" => maximalRealSubfield D.host.E

def belowE (v : PlE D.host) : HeightOneSpectrum (𝓞 Fp) where
  asIdeal := v.asIdeal.comap (algebraMap (𝓞 Fp) (𝓞 D.host.E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)

theorem fixed_of_cO {x : 𝓞 D.host.E} (hx : cO x = x) : ∃ y : 𝓞 Fp, algebraMap (𝓞 Fp) (𝓞 D.host.E) y = x :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hx




theorem exists_splitPlace (v : PlE D.host) (x0 : 𝓞 D.host.E) (hx0 : x0 ∈ v.asIdeal) (hc0 : cO x0 ∉ v.asIdeal) :
    ∃ s : SplitPlace D.host.E, s.v = belowE v := by
  exact _root_.GlobalTheory.SplitConjPlace.exists_splitPlace v x0 hx0 hc0

theorem splitEx_of_star (hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x) : SplitEx D := by
  apply GlobalTheory.SplitConjPlace.splitEx_of_star <;> assumption

end Formalism.L2
