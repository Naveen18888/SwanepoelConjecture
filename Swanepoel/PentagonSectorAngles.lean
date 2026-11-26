module
public import Swanepoel.UnitCirclePhases
public import Swanepoel.PentagonCrossingCones
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem open_halfplane_normal_count_le_three (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (axis : Plane) (haxis : ‖axis‖=1) :
    ((Finset.univ : Finset (Fin 5)).filter (fun i => 0 < inner ℝ axis (P.normal i))).card≤3 := by
  have hne : axis≠0 := by intro h; rw [h,norm_zero] at haxis; norm_num at haxis
  have hneg := G.defect_two_semicircle_ports ht F hF hdegree (-axis) (neg_ne_zero.mpr hne)
  have hinj : Function.Injective P.dart := by
    intro i j h
    exact P.vertex_injective (congrArg (fun e : OrientedEdge G => e.val.1) h)
  have hports : G.faceSourcePorts F=Finset.univ.image P.dart := P.darts.symm
  rw [hports,Finset.filter_image,Finset.card_image_of_injective _ hinj] at hneg
  let A := (Finset.univ : Finset (Fin 5)).filter (fun i => 0 < inner ℝ axis (P.normal i))
  let B := (Finset.univ : Finset (Fin 5)).filter (fun i => inner ℝ axis (P.normal i)<0)
  have hB : 2≤B.card := by
    convert hneg using 1
    congr 1
    ext i
    simp only [B,normal,Finset.mem_filter,Finset.mem_univ,true_and,inner_neg_left,neg_pos]
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hi).2.not_gt (Finset.mem_filter.mp hj).2
  have hU : (A∪B).card≤5 := by
    exact Finset.card_le_univ (A∪B)
  rw [Finset.card_union_of_disjoint hdis] at hU
  change A.card≤3
  omega

structure SectorAngleData (j : Fin 5) where
  rho : ℝ
  a : ℝ
  b : ℝ
  g : ℝ
  a_pos : 0<a
  a_lt_two : a<2
  b_pos : 0<b
  b_lt_two : b<2
  g_pos : 0<g
  g_lt_two : g<2
  phase_base : unitAngleVector rho=P.normal (j+4)
  phase_prev : unitAngleVector (rho+a)=P.normal (j+3)
  phase_next : unitAngleVector (rho-g)=P.normal j
  phase_next_next : unitAngleVector (rho-g-b)=P.normal (j+1)
  pair_left : 2≤a+g
  pair_right : 2≤b+g
  triple : 3≤a+b+g

theorem exists_sector_angle_data (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (j : Fin 5) : Nonempty (P.SectorAngleData j) := by
  obtain ⟨rho,hbase⟩ := exists_unitAngleVector (P.normal (j+4)) (P.normal_norm _)
  have h34 : (j+3)+1=j+4 := by rw [add_assoc]; rfl
  have h40 : (j+4)+1=j := by fin_cases j <;> decide
  have h32 : (j+3)+2=j := by fin_cases j <;> decide
  have h42 : (j+4)+2=j+1 := by fin_cases j <;> decide
  have hprevCross := P.normal_clockwise_turn ht hF (j+3)
  rw [h34] at hprevCross
  have hprevDot := P.normal_adjacent_inner_gt_neg_half ht (j+3)
  rw [h34] at hprevDot
  obtain ⟨a,ha0,ha2,hprev⟩ := counterclockwise_unitAngle_gap rho (P.normal (j+3)) (P.normal_norm _) (by
    rw [hbase]
    have hswap : cross2 (P.normal (j+4)) (P.normal (j+3))=
        -cross2 (P.normal (j+3)) (P.normal (j+4)) := by unfold cross2; ring
    rw [hswap]; linarith only [hprevCross]) (by rw [hbase,real_inner_comm]; exact hprevDot)
  have hnextCross := P.normal_clockwise_turn ht hF (j+4)
  rw [h40] at hnextCross
  have hnextDot := P.normal_adjacent_inner_gt_neg_half ht (j+4)
  rw [h40] at hnextDot
  obtain ⟨g,hg0,hg2,hnext⟩ := clockwise_unitAngle_gap rho (P.normal j) (P.normal_norm _)
    (by rw [hbase]; exact hnextCross) (by rw [hbase]; exact hnextDot)
  obtain ⟨b,hb0,hb2,hnextnext⟩ := clockwise_unitAngle_gap (rho-g) (P.normal (j+1)) (P.normal_norm _)
    (by rw [hnext]; exact P.normal_clockwise_turn ht hF j)
    (by rw [hnext]; exact P.normal_adjacent_inner_gt_neg_half ht j)
  have hag : 2≤a+g := by
    have hpair := P.normal_two_step_inner_le ht hF (j+3)
    rw [h32,← hprev,← hnext,unitAngleVector_inner,
      show Real.pi/3*((rho-g)-(rho+a))= -(Real.pi/3*(a+g)) by ring,Real.cos_neg] at hpair
    exact two_le_of_cos_le_neg_half (a+g) (by positivity) hpair
  have hbg : 2≤b+g := by
    have hpair := P.normal_two_step_inner_le ht hF (j+4)
    rw [h42,← hbase,← hnextnext,unitAngleVector_inner,
      show Real.pi/3*((rho-g-b)-rho)= -(Real.pi/3*(b+g)) by ring,Real.cos_neg] at hpair
    exact two_le_of_cos_le_neg_half (b+g) (by positivity) hpair
  have htriple : 3≤a+b+g := by
    by_contra hn
    have hsmall : a+b+g<3 := lt_of_not_ge hn
    let center := rho+(a-g-b)/2
    let axis := unitAngleVector center
    let S := (Finset.univ : Finset (Fin 5)).filter (fun i => 0 < inner ℝ axis (P.normal i))
    have hS : S.card≤3 := P.open_halfplane_normal_count_le_three ht hF hdegree axis (unitAngleVector_norm _)
    have hleft : 0 < inner ℝ axis (P.normal (j+3)) := by
      rw [← hprev]
      apply unitAngleVector_inner_pos_of_gap
      dsimp [center]
      constructor <;> linarith only [hsmall,ha0,hb0,hg0]
    have hbase' : 0 < inner ℝ axis (P.normal (j+4)) := by
      rw [← hbase]
      apply unitAngleVector_inner_pos_of_gap
      dsimp [center]
      constructor <;> linarith only [hsmall,ha0,hb0,hg0]
    have hnext' : 0 < inner ℝ axis (P.normal j) := by
      rw [← hnext]
      apply unitAngleVector_inner_pos_of_gap
      dsimp [center]
      constructor <;> linarith only [hsmall,ha0,hb0,hg0]
    have hright : 0 < inner ℝ axis (P.normal (j+1)) := by
      rw [← hnextnext]
      apply unitAngleVector_inner_pos_of_gap
      dsimp [center]
      constructor <;> linarith only [hsmall,ha0,hb0,hg0]
    have hsub : ({j+3,j+4,j,j+1} : Finset (Fin 5))⊆S := by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rcases hi with rfl | rfl | rfl | rfl
      · exact hleft
      · exact hbase'
      · exact hnext'
      · exact hright
    have hcard : ({j+3,j+4,j,j+1} : Finset (Fin 5)).card=4 := by fin_cases j <;> decide
    have hfour : 4≤S.card := by rw [← hcard]; exact Finset.card_le_card hsub
    omega
  exact ⟨{
    rho := rho, a := a, b := b, g := g
    a_pos := ha0, a_lt_two := ha2, b_pos := hb0, b_lt_two := hb2, g_pos := hg0, g_lt_two := hg2
    phase_base := hbase, phase_prev := hprev, phase_next := hnext, phase_next_next := hnextnext
    pair_left := hag, pair_right := hbg, triple := htriple
  }⟩

end PentagonFaceBoundary
end Swanepoel
