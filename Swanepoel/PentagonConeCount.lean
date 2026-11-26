module
public import Swanepoel.PentagonNormals
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem HalfOpen120Cone.inner_gt_neg_half {b x y : Plane}
    (hb : ‖b‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (hbx : HalfOpen120Cone b x) (hby : HalfOpen120Cone b y) :
    (-1/2:ℝ) < inner ℝ x y := by
  have hxp : (1/2:ℝ) ≤ inner ℝ b x := hbx.elim (fun h => h.le) (fun h => h.1.ge)
  have hyp : (1/2:ℝ) ≤ inner ℝ b y := hby.elim (fun h => h.le) (fun h => h.1.ge)
  by_contra hn
  have hxy : inner ℝ x y≤ -1/2 := le_of_not_gt hn
  have hadd := norm_add_sq_real x y
  rw [hx,hy] at hadd
  have hnorm : ‖x+y‖≤1 := by
    nlinarith only [hadd,hxy,sq_nonneg (‖x+y‖-1)]
  have hbound := real_inner_le_norm b (x+y)
  rw [hb,one_mul,inner_add_right] at hbound
  have hxeq : inner ℝ b x=1/2 := by linarith only [hxp,hyp,hbound,hnorm]
  have hyeq : inner ℝ b y=1/2 := by linarith only [hxp,hyp,hbound,hnorm]
  have hnormeq : ‖x+y‖=1 := by linarith only [hbound,hnorm,hxp,hyp]
  have hproj : inner ℝ b (x+y)=1 := by rw [inner_add_right,hxeq,hyeq]; ring
  have hzero : cross2 b (x+y)=0 := by
    have hg := cross2_sq_add_inner_sq b (x+y)
    rw [hb,hnormeq,hproj] at hg
    nlinarith only [hg]
  have hcx : 0<cross2 b x := by
    rcases hbx with h | h
    · linarith only [h,hxeq]
    · exact h.2
  have hcy : 0<cross2 b y := by
    rcases hby with h | h
    · linarith only [h,hyeq]
    · exact h.2
  rw [cross2_add_right] at hzero
  linarith only [hzero,hcx,hcy]

theorem fin_five_no_two_step_card (S : Finset (Fin 5)) (hS : ∀ i∈S,i+2∉S) : S.card≤2 := by
  have h : ∀ T : Finset (Fin 5),(∀ i∈T,i+2∉T) → T.card≤2 := by decide
  exact h S hS

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem half_open_120_normal_count (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (b : Plane) (hb : ‖b‖=1) :
    ((Finset.univ : Finset (Fin 5)).filter (fun i => HalfOpen120Cone b (P.normal i))).card≤2 := by
  apply fin_five_no_two_step_card
  intro i hi hj
  have hsmall := HalfOpen120Cone.inner_gt_neg_half hb (P.normal_norm i) (P.normal_norm (i+2))
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hlarge := P.normal_two_step_inner_le ht hF i
  linarith only [hsmall,hlarge]

end PentagonFaceBoundary

theorem PennyGraph.five_port_half_open_120_cone_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : (G.faceSourcePorts F).card=5) (b : Plane) (hb : ‖b‖=1) :
    ((G.faceSourcePorts F).filter (fun e => HalfOpen120Cone b (sourceNormal e))).card≤2 := by
  obtain ⟨P⟩ := G.five_port_face_boundary ht F hF hdegree hfive
  have hinj : Function.Injective P.dart := by
    intro i j h
    exact P.vertex_injective (congrArg (fun e : OrientedEdge G => e.val.1) h)
  have hports : Finset.univ.image P.dart=G.faceSourcePorts F := P.darts
  rw [← hports,Finset.filter_image,Finset.card_image_of_injective _ hinj]
  exact P.half_open_120_normal_count ht hF b hb

theorem PennyGraph.defect_half_open_120_cone_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (b : Plane) (hb : ‖b‖=1) :
    ((G.faceSourcePorts F).filter (fun e => HalfOpen120Cone b (sourceNormal e))).card+3≤
      (G.faceSourcePorts F).card := by
  by_cases hfive : (G.faceSourcePorts F).card=5
  · have h := G.five_port_half_open_120_cone_count ht F hF hdegree hfive b hb
    omega
  · have hmin := G.defect_source_ports_five_le ht F hF
    exact G.large_defect_half_open_120_cone_count ht F hF (by omega) b hb

end Swanepoel
