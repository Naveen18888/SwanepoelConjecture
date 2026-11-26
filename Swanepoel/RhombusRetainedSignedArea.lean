module
public import Swanepoel.FaceSignedArea
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem RhombusCell.displacementLinear_cross {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (w : TrackComponent G→ℝ) (x y : Plane) :
    cross2 (C.displacementLinear w x) (C.displacementLinear w y)=
      w (edgeComponent C.edgeAB)*w (edgeComponent C.edgeAD)*cross2 x y := by
  have hn := C.cross_ne_zero ht
  change cross2
    (C.portCoordULinear x • trackDisplacement w C.edgeAB+C.portCoordVLinear x • trackDisplacement w C.edgeAD)
    (C.portCoordULinear y • trackDisplacement w C.edgeAB+C.portCoordVLinear y • trackDisplacement w C.edgeAD)=_
  simp only [RhombusCell.portCoordULinear,RhombusCell.portCoordVLinear,LinearMap.coe_mk,
    AddHom.coe_mk,trackDisplacement]
  change cross2
    ((cross2 x C.v/cross2 C.u C.v) • (w (edgeComponent C.edgeAB) • C.u)+
      (cross2 C.u x/cross2 C.u C.v) • (w (edgeComponent C.edgeAD) • C.v))
    ((cross2 y C.v/cross2 C.u C.v) • (w (edgeComponent C.edgeAB) • C.u)+
      (cross2 C.u y/cross2 C.u C.v) • (w (edgeComponent C.edgeAD) • C.v))=_
  conv_rhs => rw [← cramer_reconstruct C.u C.v x hn,← cramer_reconstruct C.u C.v y hn]
  simp only [cross2_add_left,cross2_add_right,cross2_smul_left,cross2_smul_right,cross2_self]
  ring

theorem PennyGraph.retained_rhombus_signed_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (A : Finset (TrackComponent G)) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement A e)
    (F : PlaneFace G) (C : RhombusCell G) (hface : F.val=C.openRegion) :
    G.faceSignedArea P F=
      if edgeComponent C.edgeAB∈A ∧ edgeComponent C.edgeAD∈A then G.faceSignedArea G.point F else 0 := by
  let w (c : TrackComponent G) : ℝ := if c∈A then 1 else 0
  let L := C.displacementLinear w
  have heq : G.faceSignedArea P F=G.faceSignedArea (fun v => L (G.point v)) F := by
    apply G.faceSignedArea_eq_of_edge_differences
    intro e he
    rw [hP,← map_sub]
    have heF := (Finset.mem_filter.mp he).2
    obtain ⟨ha,hb⟩ := C.incident_edge_endpoints ht e
      ((congrArg Subtype.val heF).trans hface)
    exact (C.displacementLinear_on_inside_edge ht w e ha hb).symm
  have hscale : G.faceSignedArea (fun v => L (G.point v)) F=
      w (edgeComponent C.edgeAB)*w (edgeComponent C.edgeAD)*G.faceSignedArea G.point F := by
    unfold PennyGraph.faceSignedArea
    simp_rw [show ∀ a b, cross2 (L (G.point a)) (L (G.point b))=
      w (edgeComponent C.edgeAB)*w (edgeComponent C.edgeAD)*cross2 (G.point a) (G.point b)
      from fun a b => C.displacementLinear_cross ht w _ _]
    rw [← Finset.mul_sum]
    ring
  rw [heq,hscale]
  by_cases ha : edgeComponent C.edgeAB∈A <;> by_cases hb : edgeComponent C.edgeAD∈A <;> simp [w,ha,hb]

end Swanepoel
