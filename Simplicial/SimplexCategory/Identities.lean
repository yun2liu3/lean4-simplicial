import Simplicial.SimplexCategory.Generators

/-!
# Simplicial Identities

We prove the five simplicial identities relating face maps `δ` and degeneracy maps `σ`.
-/

open CategoryTheory
open Simplicial

namespace SimplexCategory

-- Helper: convert succAbove to ℕ arithmetic
private theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  simp [Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ, apply_ite Fin.val]

-- Helper: convert predAbove to ℕ arithmetic
private theorem val_predAbove {n : ℕ} (p : Fin n) (k : Fin (n + 1)) :
    (p.predAbove k).val = if p.val < k.val then k.val - 1 else k.val := by
  simp [Fin.predAbove, Fin.lt_iff_val_lt_val, Fin.coe_castSucc, apply_dite Fin.val,
    Fin.coe_pred, Fin.coe_castPred]

/-- Face-degeneracy identity: `δ (castSucc i) ≫ σ i = 𝟙`. -/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  ext k; simp [δ, σ]

/-- Face-degeneracy identity: `δ (i+1) ≫ σ i = 𝟙`. -/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} :
    δ i.succ ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  ext k; simp [δ, σ]
  simp only [val_succAbove, val_predAbove, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> omega

/-- Face-face identity: for `i ≤ j`, `δ i ≫ δ (j+1) = δ j ≫ δ (castSucc i)`. -/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ (Fin.castSucc i) := by
  ext k; simp [δ]
  simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> omega

/-- Face-degeneracy identity: for `i ≤ castSucc j`,
  `δ (castSucc i) ≫ σ (j+1) = σ j ≫ δ i`. -/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    δ (Fin.castSucc i) ≫ σ j.succ = σ j ≫ δ i := by
  have hH : (i : ℕ) ≤ j := by exact_mod_cast H
  ext k; simp [δ, σ]
  simp only [val_succAbove, val_predAbove, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> omega

/-- Degeneracy-degeneracy identity: for `i ≤ j`,
  `σ (castSucc i) ≫ σ j = σ (j+1) ≫ σ i`. -/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext k; simp [σ]
  simp only [val_predAbove, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> omega

end SimplexCategory
