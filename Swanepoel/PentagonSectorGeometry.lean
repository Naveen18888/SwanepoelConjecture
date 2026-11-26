module
public import Swanepoel.PentagonSectorTransitions
@[expose] public section

noncomputable section
namespace Swanepoel

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

def SectorStep (normal : Plane) (a b : Fin 5) : Prop :=
  (b=a+1 ∧ inner ℝ (carriedVector (P.dart a)) normal< -Real.sqrt 3/2) ∨
    (a=b+1 ∧ Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart b)) normal)

theorem two_step_sharp_positive_impossible (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (normal : Plane) (hn : ‖normal‖=1) (i : Fin 5)
    (hi : Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart i)) normal)
    (hj : Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart (i+2))) normal) : False := by
  have hsqrt : (1/2:ℝ)<Real.sqrt 3/2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hsmall := three_unit_chain_inner_gt_neg_half (carriedVector (P.dart i)) normal
    (carriedVector (P.dart (i+2))) (carriedVector_norm _) hn (carriedVector_norm _)
    (lt_trans hsqrt hi) (by rw [real_inner_comm]; exact lt_trans hsqrt hj)
  have hlarge := P.normal_two_step_inner_le ht hF i
  rw [P.normal_inner] at hlarge
  linarith only [hsmall,hlarge]

theorem two_step_sharp_negative_impossible (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (normal : Plane) (hn : ‖normal‖=1) (i : Fin 5)
    (hi : inner ℝ (carriedVector (P.dart i)) normal< -Real.sqrt 3/2)
    (hj : inner ℝ (carriedVector (P.dart (i+2))) normal< -Real.sqrt 3/2) : False := by
  apply P.two_step_sharp_positive_impossible ht hF (-normal) (by simpa only [norm_neg] using hn) i
  · rw [inner_neg_right]; linarith only [hi]
  · rw [inner_neg_right]; linarith only [hj]

theorem no_three_sector_steps (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (normal : Plane) (hn : ‖normal‖=1) (a b c d : Fin 5)
    (hab : P.SectorStep normal a b) (hbc : P.SectorStep normal b c) (hcd : P.SectorStep normal c d) : False := by
  have hsqrt := Real.sqrt_nonneg (3:ℝ)
  rcases hab with ⟨hb,h0⟩ | ⟨ha,h0⟩
  · rcases hbc with ⟨hc,h1⟩ | ⟨hc,h1⟩
    · rcases hcd with ⟨_,h2⟩ | ⟨hd,h2⟩
      · have hca : c=a+2 := by rw [hc,hb,add_assoc]; rfl
        rw [hca] at h2
        exact P.two_step_sharp_negative_impossible ht hF normal hn a h0 h2
      · have hbd : b=d := add_right_cancel (hc.symm.trans hd)
        rw [← hbd] at h2
        linarith only [h1,h2,hsqrt]
    · have hac : a=c := add_right_cancel (hb.symm.trans hc)
      rw [← hac] at h1
      linarith only [h0,h1,hsqrt]
  · rcases hbc with ⟨_,h1⟩ | ⟨hc,h1⟩
    · linarith only [h0,h1,hsqrt]
    · rcases hcd with ⟨_,h2⟩ | ⟨hd,h2⟩
      · linarith only [h1,h2,hsqrt]
      · have hbd : b=d+2 := by rw [hc,hd,add_assoc]; rfl
        rw [hbd] at h0
        exact P.two_step_sharp_positive_impossible ht hF normal hn d h2 h0

inductive SectorWalk (normal : Plane) : Fin 5→Fin 5→ℕ→Prop
  | nil (a : Fin 5) : SectorWalk normal a a 0
  | cons {a b c : Fin 5} {k : ℕ} : P.SectorStep normal a b → SectorWalk normal b c k →
      SectorWalk normal a c (k+1)

theorem SectorWalk.length_le_two {normal : Plane} {a b : Fin 5} {k : ℕ}
    (h : P.SectorWalk normal a b k) (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (hn : ‖normal‖=1) : k≤2 := by
  cases h with
  | nil => omega
  | cons h1 htail =>
    cases htail with
    | nil => omega
    | cons h2 htail =>
      cases htail with
      | nil => omega
      | cons h3 _ => exact False.elim (P.no_three_sector_steps ht hF normal hn _ _ _ _ h1 h2 h3)

end PentagonFaceBoundary
end Swanepoel
