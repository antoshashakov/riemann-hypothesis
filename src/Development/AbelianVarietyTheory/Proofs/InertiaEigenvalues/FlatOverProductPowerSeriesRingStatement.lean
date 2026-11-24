module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.flat_over_product_power_series_ring : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E] [Algebra (LetA O n) E] (p : ℕ), IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E := by
  first | exact @GlobalTheory.FlatLocCompl.flat_letA | exact GlobalTheory.FlatLocCompl.flat_letA | (intros; apply GlobalTheory.FlatLocCompl.flat_letA <;> assumption)
