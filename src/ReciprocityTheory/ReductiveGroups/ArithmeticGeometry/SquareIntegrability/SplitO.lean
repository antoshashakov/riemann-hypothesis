module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitOA

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def soPsi (x : E) : EuclideanSpace ℂ (E →+* ℂ) := WithLp.toLp 2 fun σ => σ x

theorem soPsi_add (x y : E) : soPsi (x + y) = soPsi x + soPsi y := by
  ext σ
  change σ (x + y) = σ x + σ y
  exact map_add σ x y

theorem soPsi_zero : soPsi (0 : E) = 0 := by
  ext σ
  change σ 0 = 0
  exact map_zero σ

theorem so_li_complex :
    LinearIndependent ℂ (fun i => soPsi (RingOfIntegers.basis E i : E)) := by
  classical
  let T : ((E →+* ℂ) → ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ) :=
    { toFun := fun v i => ∑ σ, v σ * σ (RingOfIntegers.basis E i : E)
      map_add' := fun v v' => by ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by ext i; simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    exact so_emb_inj v (fun i => congr_fun hv i)
  have hsurj : Function.Surjective T := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [Module.finrank_fintype_fun_eq_card, NumberField.Embeddings.card,
      ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hσ : ∀ σ : E →+* ℂ, ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0 := by
    intro σ
    have := congr_arg (fun v : EuclideanSpace ℂ (E →+* ℂ) => v σ) hc
    simpa [soPsi, WithLp.ofLp_toLp] using this
  obtain ⟨v, hv⟩ := hsurj (Pi.single i 1)
  have h0 : ∑ j, c j * T v j = 0 := by
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have h1 : v σ * ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0 := by rw [hσ σ, mul_zero]
    rw [Finset.mul_sum] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hv] at h0
  simpa [Pi.single_apply] using h0

theorem so_sum_emb (x : E) : ∑ σ : E →+* ℂ, σ x = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _
    fun σ => by simp [RingHom.equivRatAlgHom_apply]

end

end ReciprocityTheory.ChartRestriction.G.I2
