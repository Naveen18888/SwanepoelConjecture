module
public import Swanepoel.Definitions
@[expose] public section

noncomputable section
namespace Swanepoel

def N (x : ℤ) : ℤ := x ^ 2 / 4

theorem N_nonneg (x : ℤ) : 0 ≤ N x := Int.ediv_nonneg (sq_nonneg x) (by decide)

theorem N_shift_two (x : ℤ) : N (x + 2) = N x + x + 1 := by
  unfold N
  have h : (x + 2) ^ 2 = x ^ 2 + (x + 1) * 4 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by decide : (4 : ℤ) ≠ 0)]
  ring

theorem N_complete_square (K a s : ℤ) :
    N (K + a) = a * s + s * (K - s) + N (K + a - 2 * s) := by
  unfold N
  have h : (K + a) ^ 2 = (K + a - 2 * s) ^ 2 +
      (a * s + s * (K - s)) * 4 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by decide : (4 : ℤ) ≠ 0)]
  ring

theorem low_crossing_bound (K a s R : ℤ) (ha : 0 ≤ a)
    (hR : 10000 * R ≤ 2379 * K ^ 2) (hs : 100 * s ≤ 61 * K) :
    R + a * s ≤ N (K + a) := by
  unfold N
  apply (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 4)).mpr
  have hm := mul_nonneg ha (sub_nonneg.mpr hs)
  nlinarith [sq_nonneg (50 * a - 11 * K)]

structure BlockCounts where
  n : ℕ
  m : ℕ
  q : ℕ
  f : ℕ
  T : ℕ
  x : ℤ
  tracks : (m : ℤ) - T = 2 * q
  euler : (n : ℤ) - m + (q + f) = 1
  effective : x = (T : ℤ) - 2 * f
  effective_nonneg : 0 ≤ x

theorem block_bound (C : BlockCounts) (hq : (C.q : ℤ) + C.f ≤ N C.x) :
    (C.m : ℤ) ≤ extremalValue C.n := by
  have hn : (C.n : ℤ) = (C.q : ℤ) + C.f + C.x + 1 := by
    linear_combination C.euler + C.tracks - C.effective
  have hd : 2 * (C.n : ℤ) - C.m = C.x + 2 := by
    linear_combination 2 * C.euler + C.tracks - C.effective
  have hN : (C.n : ℤ) ≤ N (C.x + 2) := by rw [N_shift_two]; omega
  have hsq : 4 * (C.n : ℤ) ≤ (C.x + 2) ^ 2 := by
    unfold N at hN
    have hm := (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 4)).mp hN
    nlinarith
  have hsqr : 4 * (C.n : ℝ) ≤ ((C.x : ℝ) + 2) ^ 2 := by exact_mod_cast hsq
  have hx : (0 : ℝ) ≤ (C.x : ℝ) := by exact_mod_cast C.effective_nonneg
  have hs := Real.sq_sqrt (Nat.cast_nonneg C.n : (0 : ℝ) ≤ C.n)
  have hsn := Real.sqrt_nonneg (C.n : ℝ)
  have hroot : 2 * Real.sqrt C.n ≤ (C.x : ℝ) + 2 := by nlinarith
  have hdr : 2 * (C.n : ℝ) - C.m = (C.x : ℝ) + 2 := by exact_mod_cast hd
  unfold extremalValue
  apply Int.le_floor.mpr
  simp only [Int.cast_natCast]
  nlinarith

end Swanepoel
