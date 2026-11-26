module
public import Swanepoel.HalfLocalCutLoop
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PositiveSpineChain.bankLabel_constant_of_disjoint {n : ℕ} {G : PennyGraph n}
    {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (loop : PlaneChain (edgeCenter s) (edgeCenter s)) (sign : ℝ)
    (hdis : Disjoint (p.bankRegion sign) loop.trace)
    {z : Plane} (hz : z∈p.bankRegion sign) :
    loop.windingIndex z=p.bankLabel loop sign := by
  have hbase : edgeCenter s+(sign/4) • carriedVector s∈p.bankRegion sign := by
    refine ⟨edgeCenter s,p.toPlane.start_mem_trace,1/4,⟨by norm_num,by norm_num⟩,?_⟩
    congr 2
    ring
  exact loop.windingIndex_constant (p.bankRegion_preconnected sign) hdis hz hbase

theorem PositiveSpineChain.cellPoint_mem_bank_of_segment {n : ℕ} {G : PennyGraph n}
    {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (C : RhombusCell G) (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c))
    (hv : carriedVector s=C.u)
    (hseg : segment ℝ (edgeCenter e) (edgeCenter f)⊆p.toPlane.trace)
    (sign δ r : ℝ) (hδ : δ∈Ioc (0:ℝ) (1/2)) (hr : r∈Icc (0:ℝ) 1) :
    C.cellPoint (1/2+sign*δ) r∈p.bankRegion sign := by
  have hcorn : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hm : C.cellPoint (1/2) r∈segment ℝ (edgeCenter e) (edgeCenter f) := by
    rw [segment_eq_image]
    refine ⟨r,hr,?_⟩
    simp only [edgeCenter,hE,hF,RhombusCell.midpoint2,RhombusCell.cellPoint,RhombusCell.u,RhombusCell.v]
    rw [hcorn]
    module
  refine ⟨C.cellPoint (1/2) r,hseg hm,δ,hδ,?_⟩
  rw [hv]
  dsimp [RhombusCell.cellPoint]
  module

theorem PositiveSpineChain.open_cell_bank_of_segment {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (C : RhombusCell G) (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c))
    (hv : carriedVector s=C.u)
    (hseg : segment ℝ (edgeCenter e) (edgeCenter f)⊆p.toPlane.trace)
    {z : Plane} (hz : z∈C.openRegion) :
    (1/2<C.coordU z → z∈p.bankRegion 1) ∧
      (C.coordU z<1/2 → z∈p.bankRegion (-1)) := by
  have hq : C.coordV z∈Icc (0:ℝ) 1 := ⟨hz.2.2.1.le,hz.2.2.2.le⟩
  constructor
  · intro hside
    have hd : C.coordU z-1/2∈Ioc (0:ℝ) (1/2) := ⟨by linarith,by linarith [hz.2.1]⟩
    have hm := p.cellPoint_mem_bank_of_segment C hE hF hv hseg 1 (C.coordU z-1/2) (C.coordV z) hd hq
    rw [show (1/2:ℝ)+1*(C.coordU z-1/2)=C.coordU z by ring,C.reconstruct ht z] at hm
    exact hm
  · intro hside
    have hd : 1/2-C.coordU z∈Ioc (0:ℝ) (1/2) := ⟨by linarith,by linarith [hz.1]⟩
    have hm := p.cellPoint_mem_bank_of_segment C hE hF hv hseg (-1) (1/2-C.coordU z) (C.coordV z) hd hq
    rw [show (1/2:ℝ)+(-1)*(1/2-C.coordU z)=C.coordU z by ring,C.reconstruct ht z] at hm
    exact hm

theorem PositiveSpineChain.bankLabel_difference_of_disjoint {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (loop : PlaneChain (edgeCenter s) (edgeCenter s))
    (hdis : ∀ sign : ℝ, sign=1 ∨ sign= -1 → Disjoint (p.bankRegion sign) loop.trace)
    (hse : Relation.ReflTransGen PositiveCellStep s e)
    (hseg : segment ℝ (edgeCenter e) (edgeCenter f)⊆p.toPlane.trace)
    (hef : PositiveCellStep e f) (ε : ℝ) (hε : 0<ε)
    (hjump : ∀ r : ℝ, 0<r → r<ε →
      loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) (-r))=
        loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) r)+1) :
    p.bankLabel loop (-1)=p.bankLabel loop 1+1 := by
  obtain ⟨C,hE,hF,hpos⟩ := hef
  have hv : carriedVector s=C.u := by
    rw [positive_path_vector_eq hse]
    simp only [carriedVector,hE,RhombusCell.u]
  have heq : e=C.edgeAB := Subtype.ext hE
  have hfq : f=C.edgeDC := Subtype.ext hF
  have hm : windingNormalProbe (edgeCenter e) (edgeCenter f) 0=C.center := by
    have hh : stepCenter e f=C.center := by rw [heq,hfq,C.stepCenter_eq]
    simpa only [windingNormalProbe,zero_smul,add_zero,stepCenter,RhombusCell.midpoint2] using hh
  have hopen : IsOpen {r : ℝ | windingNormalProbe (edgeCenter e) (edgeCenter f) r∈C.openRegion} :=
    C.isOpen_openRegion.preimage (continuous_windingNormalProbe _ _)
  have hzero : (0:ℝ)∈{r : ℝ | windingNormalProbe (edgeCenter e) (edgeCenter f) r∈C.openRegion} := by
    rw [Set.mem_ofPred_eq,hm,← C.cellPoint_half_eq_center]
    exact C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let r := min ε δ/2
  have hr : 0<r := by dsimp [r]; positivity
  have hrε : r<ε := by have := min_le_left ε δ; dsimp [r]; linarith
  have hrδ : r<δ := by have := min_le_right ε δ; dsimp [r]; linarith
  have hp : windingNormalProbe (edgeCenter e) (edgeCenter f) r∈C.openRegion :=
    hball (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hr] using hrδ)
  have hn : windingNormalProbe (edgeCenter e) (edgeCenter f) (-r)∈C.openRegion :=
    hball (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_neg,abs_of_pos hr] using hrδ)
  have hcoordP := PositiveCellStep.winding_probe_coordU ht C hE hF r
  have hcoordN := PositiveCellStep.winding_probe_coordU ht C hE hF (-r)
  have hP : windingNormalProbe (edgeCenter e) (edgeCenter f) r∈p.bankRegion 1 :=
    (p.open_cell_bank_of_segment ht C hE hF hv hseg hp).1 (by rw [hcoordP]; linarith [div_pos hr hpos])
  have hN : windingNormalProbe (edgeCenter e) (edgeCenter f) (-r)∈p.bankRegion (-1) :=
    (p.open_cell_bank_of_segment ht C hE hF hv hseg hn).2 (by
      rw [hcoordN]
      have := div_neg_of_neg_of_pos (neg_neg_of_pos hr) hpos
      linarith)
  have hj := hjump r hr hrε
  rw [p.bankLabel_constant_of_disjoint loop (-1) (hdis (-1) (Or.inr rfl)) hN,
    p.bankLabel_constant_of_disjoint loop 1 (hdis 1 (Or.inl rfl)) hP] at hj
  exact hj

end Swanepoel
