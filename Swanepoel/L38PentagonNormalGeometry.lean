module
public import Swanepoel.PentagonCrossingCones
public import Swanepoel.UnitCapGeometry
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators

theorem l38_three_normals_clockwise (a b c : Plane)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1)
    (hab : cross2 a b<0) (hbc : cross2 b c<0)
    (hac : inner ℝ a c≤ -1/2) (hsum : 1<‖a+b+c‖) : cross2 a c<0 := by
  by_contra hn
  have hnonneg : 0≤cross2 a c := le_of_not_gt hn
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · have hz : cross2 a c=0 := hzero.symm
    rcases unit_cross_zero_eq_or_neg a c ha hc hz with h | h
    · rw [h,real_inner_self_eq_norm_sq,ha] at hac
      norm_num at hac
    · have heq : a+b+c=b := by rw [h]; abel
      rw [heq,hb] at hsum
      exact lt_irrefl _ hsum
  · have hswap : cross2 (-b) c= -cross2 b c := by unfold cross2; simp; ring
    have hneg : cross2 a (-b)= -cross2 a b := by unfold cross2; simp; ring
    let r := cross2 (-b) c/cross2 a c
    let s := cross2 a (-b)/cross2 a c
    have hr : 0≤r := (div_pos (by rw [hswap]; linarith) hpos).le
    have hs : 0≤s := (div_pos (by rw [hneg]; linarith) hpos).le
    have heq : -b=r • a+s • c := (cramer_reconstruct a c (-b) (ne_of_gt hpos)).symm
    have hfar : 1≤‖(-b)-(a+c)‖ := by
      have he : (-b)-(a+c)= -(a+b+c) := by abel
      rw [he,norm_neg]
      exact hsum.le
    rcases unit_cone_far_corner (-b) a c (by simpa using hb) ha hc
        (ne_of_gt hpos) r s hr hs heq hfar with h | h
    · have hz : cross2 a b=0 := by rw [← h,cross2_neg_left,cross2_self,neg_zero]
      linarith only [hz,hab]
    · have hz : cross2 b c=0 := by rw [← h]; simp [cross2]; ring
      linarith only [hz,hbc]

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem normal_two_step_clockwise (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (i : Fin 5) : cross2 (P.normal i) (P.normal (i+2))<0 := by
  have hrotate : (∑ k : Fin 5,P.normal (i+k))=0 :=
    (Equiv.sum_comp (Equiv.addLeft i) P.normal).trans (P.normal_sum ht hF)
  have hbalance : P.normal i+P.normal (i+1)+P.normal (i+2)=
      -(P.normal (i+3)+P.normal (i+4)) := by
    norm_num [Fin.sum_univ_succ] at hrotate
    apply eq_neg_iff_add_eq_zero.mpr
    convert hrotate using 1
    abel
  have hidx : (i+3)+1=i+4 := by rw [add_assoc]; rfl
  have hdot := P.normal_adjacent_inner_gt_neg_half ht (i+3)
  rw [hidx] at hdot
  have hnorm := norm_add_sq_real (P.normal (i+3)) (P.normal (i+4))
  rw [P.normal_norm,P.normal_norm] at hnorm
  have hlarge : 1<‖P.normal i+P.normal (i+1)+P.normal (i+2)‖ := by
    rw [hbalance,norm_neg]
    nlinarith only [hnorm,hdot,norm_nonneg (P.normal (i+3)+P.normal (i+4))]
  apply l38_three_normals_clockwise _ _ _ (P.normal_norm _) (P.normal_norm _) (P.normal_norm _)
    (P.normal_clockwise_turn ht hF i) ?_ (P.normal_two_step_inner_le ht hF i) hlarge
  simpa only [add_assoc,show (1:Fin 5)+1=2 by decide] using P.normal_clockwise_turn ht hF (i+1)

end PentagonFaceBoundary
end Swanepoel
