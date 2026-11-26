module
public import Swanepoel.UnitCapGeometry
public import Swanepoel.DefectBoundary
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.unit_cap_forces_rhombus {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (a b c d : Fin n)
    (hab : G.graph.Adj a b) (hac : G.graph.Adj a c) (hbd : G.graph.Adj b d)
    (axis : Plane →ₗ[ℝ] ℝ)
    (habAxis : 0 < axis (G.point b-G.point a))
    (hacAxis : 0 ≤ axis (G.point c-G.point a))
    (hbdAxis : axis (G.point d-G.point b) ≤ 0)
    (hind : cross2 (G.point b-G.point a) (G.point d-G.point b) ≠ 0)
    (hside : 0 < cross2 (G.point b-G.point a) (G.point c-G.point a) /
      cross2 (G.point b-G.point a) (G.point d-G.point b)) :
    ∃ C : RhombusCell G, C.a=a ∧ C.b=b ∧ C.c=d ∧ C.d=c ∧
      G.point c-G.point a=G.point d-G.point b ∧ axis (G.point c-G.point a)=0 := by
  have hcd : c ≠ d := by
    intro he
    subst d
    exact ht a b c hab hbd hac.symm
  have hfar : 1 ≤ ‖(G.point c-G.point a)-
      ((G.point b-G.point a)+(G.point d-G.point b))‖ := by
    have he : (G.point c-G.point a)-
        ((G.point b-G.point a)+(G.point d-G.point b))=G.point c-G.point d := by abel
    rw [he, ← dist_eq_norm]
    exact G.separated c d hcd
  obtain ⟨hmatch,hzero⟩ := unit_cap_neighbours_match
    (G.point c-G.point a) (G.point b-G.point a) (G.point d-G.point b)
    (by simpa only [← dist_eq_norm] using hac.symm.2)
    (by simpa only [← dist_eq_norm] using hab.symm.2)
    (by simpa only [← dist_eq_norm] using hbd.symm.2)
    axis habAxis hacAxis hbdAxis hind hside hfar
  have hcontact : G.graph.Adj c d := by
    have he : G.point d-G.point c=G.point b-G.point a := by
      calc
        _ = (G.point d-G.point b)-(G.point c-G.point a)+
            (G.point b-G.point a) := by abel
        _ = _ := by rw [← hmatch]; abel
    refine ⟨hcd,?_⟩
    rw [dist_comm,dist_eq_norm,he,← dist_eq_norm]
    exact hab.symm.2
  have had : a ≠ d := by
    intro he
    apply hind
    rw [← he]
    have hn : G.point a-G.point b=-(G.point b-G.point a) := by abel
    rw [hn]
    simp only [cross2,PiLp.neg_apply]
    ring
  have hbc : b ≠ c := by
    intro he
    have hz : cross2 (G.point b-G.point a) (G.point c-G.point a)=0 := by
      rw [← he,cross2_self]
    rw [hz,zero_div] at hside
    exact lt_irrefl _ hside
  let C : RhombusCell G := ⟨a,b,d,c,had,hbc,hab,hbd,hcontact.symm,hac.symm⟩
  exact ⟨C,rfl,rfl,rfl,rfl,hmatch,hzero⟩

theorem PennyGraph.unit_cap_reverse_not_source {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (a b c d : Fin n)
    (hab : G.graph.Adj a b) (hac : G.graph.Adj a c) (hbd : G.graph.Adj b d)
    (axis : Plane →ₗ[ℝ] ℝ)
    (habAxis : 0 < axis (G.point b-G.point a))
    (hacAxis : 0 ≤ axis (G.point c-G.point a))
    (hbdAxis : axis (G.point d-G.point b) ≤ 0)
    (hpos : 0 < cross2 (G.point b-G.point a) (G.point d-G.point b))
    (hside : 0 < cross2 (G.point b-G.point a) (G.point c-G.point a) /
      cross2 (G.point b-G.point a) (G.point d-G.point b)) :
    ¬ SpineSource (⟨(b,a),hab.symm⟩ : OrientedEdge G) := by
  obtain ⟨C,ha,hb,hc,hd,_,_⟩ := G.unit_cap_forces_rhombus ht a b c d
    hab hac hbd axis habAxis hacAxis hbdAxis (ne_of_gt hpos) hside
  let D : RhombusCell G := ⟨b,a,c,d,by simpa only [hb,hd] using C.bd,
    by simpa only [ha,hc] using C.ac,hab.symm,hac,
    by simpa only [hc,hd] using C.cd.symm,hbd.symm⟩
  have hDneg : cross2 D.u D.v < 0 := by
    change cross2 (G.point a-G.point b) (G.point d-G.point b) < 0
    have hn : G.point a-G.point b=-(G.point b-G.point a) := by abel
    rw [hn,cross2_neg_left]
    linarith
  have hface := G.sourceFace_eq_rhombus_of_negative_ab ht
    (⟨(b,a),hab.symm⟩ : OrientedEdge G) D rfl hDneg
  intro hsource
  exact G.sourceFace_ne_rhombus ht _ hsource D hface

end Swanepoel
