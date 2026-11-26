module
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_dft_conjugate {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    (starRingEnd ℂ) (ZMod.dft f k) =
      ∑ j : ZMod N, ZMod.stdAddChar (j*k) * (starRingEnd ℂ) (f j) := by
  rw [ZMod.dft_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul, map_mul]
  have hchar : (starRingEnd ℂ) (ZMod.stdAddChar (-(j*k))) = ZMod.stdAddChar (j*k) := by
    simpa only [neg_neg] using
      (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) (-(j*k))).symm
  rw [hchar]

theorem finite_dft_inverse_sum {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (j : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (j*k) * ZMod.dft f k) = (N : ℂ)*f j := by
  have h := congrFun (ZMod.dft_dft f) (-j)
  simpa only [ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul, mul_comm] using h

theorem finite_dft_inner {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    (∑ k : ZMod N, (starRingEnd ℂ) (ZMod.dft f k) * ZMod.dft g k) =
      (N : ℂ) * ∑ j : ZMod N, (starRingEnd ℂ) (f j) * g j := by
  calc
    _ = ∑ k : ZMod N, ∑ j : ZMod N,
        (ZMod.stdAddChar (j*k) * (starRingEnd ℂ) (f j)) * ZMod.dft g k := by
      simp only [finite_dft_conjugate, Finset.sum_mul]
    _ = ∑ j : ZMod N, ∑ k : ZMod N,
        (starRingEnd ℂ) (f j) * (ZMod.stdAddChar (j*k) * ZMod.dft g k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j : ZMod N, (starRingEnd ℂ) (f j) * ((N : ℂ)*g j) := by
      simp only [← Finset.mul_sum, finite_dft_inverse_sum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem finite_dft_parseval {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖ZMod.dft f k‖^2) = (N : ℝ)*∑ j : ZMod N, ‖f j‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.conj_mul'] using finite_dft_inner f f

theorem finite_dft_cyclic_shift {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun j => f (j+1)) k = ZMod.stdAddChar k * ZMod.dft f k := by
  calc
    _ = ∑ j : ZMod N, ZMod.stdAddChar (-(j*k)) * f (j+1) := by
      simp only [ZMod.dft_apply, smul_eq_mul]
    _ = ∑ i : ZMod N, ZMod.stdAddChar (-((i-1)*k)) * f i :=
      Fintype.sum_equiv (Equiv.addRight 1) _ _ (by intro j; simp)
    _ = _ := by
      have hphase (i : ZMod N) : -((i-1)*k) = k + -(i*k) := by ring
      simp only [hphase, AddChar.map_add_eq_mul, ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem finite_dft_cyclic_difference {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun j => f (j+1)-f j) k =
      (ZMod.stdAddChar k-1) * ZMod.dft f k := by
  have hfun : (fun j => f (j+1)-f j) = (fun j => f (j+1)) - f := rfl
  rw [hfun, map_sub]
  simp only [Pi.sub_apply, finite_dft_cyclic_shift]
  ring

theorem finite_dft_edge_energy {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (N : ℝ)*(∑ j : ZMod N, ‖f (j+1)-f j‖^2) =
      ∑ k : ZMod N, ‖ZMod.stdAddChar k-1‖^2 * ‖ZMod.dft f k‖^2 := by
  calc
    _ = ∑ k : ZMod N, ‖ZMod.dft (fun j => f (j+1)-f j) k‖^2 :=
      (finite_dft_parseval (fun j => f (j+1)-f j)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [finite_dft_cyclic_difference, norm_mul, mul_pow]

theorem finite_dft_wirtinger_of_spectral_gap {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hmean : ∑ j, f j = 0) (gap : ℝ)
    (hgap : ∀ k : ZMod N, k ≠ 0 → gap ≤ ‖ZMod.stdAddChar k-1‖^2) :
    gap*(∑ j : ZMod N, ‖f j‖^2) ≤ ∑ j : ZMod N, ‖f (j+1)-f j‖^2 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  have hzero : ZMod.dft f 0 = 0 := by rw [ZMod.dft_apply_zero, hmean]
  apply (mul_le_mul_iff_right₀ hN).mp
  calc
    _ = gap*(∑ k : ZMod N, ‖ZMod.dft f k‖^2) := by rw [finite_dft_parseval]; ring
    _ = ∑ k : ZMod N, gap*‖ZMod.dft f k‖^2 := Finset.mul_sum _ _ _
    _ ≤ ∑ k : ZMod N, ‖ZMod.stdAddChar k-1‖^2*‖ZMod.dft f k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k = 0
      · simp only [hk, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
      · exact mul_le_mul_of_nonneg_right (hgap k hk) (sq_nonneg _)
    _ = _ := (finite_dft_edge_energy f).symm

end Swanepoel
