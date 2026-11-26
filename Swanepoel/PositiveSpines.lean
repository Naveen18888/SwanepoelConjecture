module
public import Swanepoel.TrackComponents
public import Swanepoel.CellUniqueness
@[expose] public section

noncomputable section
namespace Swanepoel

theorem cross2_sub_right (e x y : Plane) : cross2 e (x-y)=cross2 e x-cross2 e y := by
  simp [cross2]
  ring

def edgeCenter {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : Plane :=
  RhombusCell.midpoint2 (G.point e.val.1) (G.point e.val.2)

def edgeHeight {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : ℝ :=
  cross2 (carriedVector e) (edgeCenter e)

def PositiveCellStep {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) : Prop :=
  ∃ C : RhombusCell G, e.val=(C.a,C.b) ∧ f.val=(C.d,C.c) ∧ 0 < cross2 C.u C.v

theorem PositiveCellStep.to_cellStep {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : PositiveCellStep e f) : CellStep e f := by
  obtain ⟨C,he,hf,_⟩ := h
  exact ⟨C,he,hf⟩

theorem PositiveCellStep.height_lt {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : PositiveCellStep e f) : edgeHeight e < edgeHeight f := by
  obtain ⟨C,he,hf,hpos⟩ := h
  have hvec := CellStep.vector_eq (show CellStep e f from ⟨C,he,hf⟩)
  have hmid : edgeCenter f-edgeCenter e=C.v := by
    simpa only [edgeCenter,he,hf] using C.spine_step
  have hu : carriedVector e=C.u := by simp only [carriedVector,he,RhombusCell.u]
  have hd : edgeHeight f-edgeHeight e=cross2 C.u C.v := by
    unfold edgeHeight
    rw [← hvec, ← cross2_sub_right,hmid,hu]
  linarith

theorem PositiveCellStep.height_gap {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f : OrientedEdge G} (h : PositiveCellStep e f) :
    Real.sqrt 3/2 < edgeHeight f-edgeHeight e := by
  obtain ⟨C,he,hf,hpos⟩ := h
  have hvec := CellStep.vector_eq (show CellStep e f from ⟨C,he,hf⟩)
  have hmid : edgeCenter f-edgeCenter e=C.v := by
    simpa only [edgeCenter,he,hf] using C.spine_step
  have hu : carriedVector e=C.u := by simp only [carriedVector,he,RhombusCell.u]
  unfold edgeHeight
  rw [← hvec, ← cross2_sub_right,hmid,hu]
  simpa only [abs_of_pos hpos] using C.area_lower ht

theorem positive_chain_height_lt {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : Relation.TransGen PositiveCellStep e f) : edgeHeight e < edgeHeight f := by
  induction h with
  | single h => exact h.height_lt
  | tail _ h ih => exact ih.trans h.height_lt

theorem no_closed_positive_spine {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    ¬ Relation.TransGen PositiveCellStep e e :=
  fun h => (lt_irrefl (edgeHeight e)) (positive_chain_height_lt h)

theorem positive_step_functional {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f g : OrientedEdge G} (hf : PositiveCellStep e f) (hg : PositiveCellStep e g) : f=g := by
  obtain ⟨C,he,hf,hC⟩ := hf
  obtain ⟨D,he',hg,hD⟩ := hg
  have hab : (C.a,C.b)=(D.a,D.b) := he.symm.trans he'
  obtain ⟨hd,hc⟩ := RhombusCell.unique_positive_side ht C D
    (congrArg Prod.fst hab) (congrArg Prod.snd hab) hC hD
  apply Subtype.ext
  rw [hf,hg,hd,hc]

theorem reverseEdge_involutive {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    reverseEdge (reverseEdge e)=e := by apply Subtype.ext; rfl

def RhombusCell.halfTurn {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : RhombusCell G where
  a := C.c
  b := C.d
  c := C.a
  d := C.b
  ac := C.ac.symm
  bd := C.bd.symm
  ab := C.cd
  bc := C.da
  cd := C.ab
  da := C.bc

theorem PositiveCellStep.reverse {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : PositiveCellStep e f) : PositiveCellStep (reverseEdge f) (reverseEdge e) := by
  obtain ⟨C,he,hf,hpos⟩ := h
  have hu : C.halfTurn.u= -C.u := by
    change G.point C.d-G.point C.c= -(G.point C.b-G.point C.a)
    rw [C.opposite_vectors]
    abel
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hv : C.halfTurn.v= -C.v := by
    change G.point C.b-G.point C.c= -(G.point C.d-G.point C.a)
    rw [hc]
    abel
  refine ⟨C.halfTurn, ?_, ?_, ?_⟩
  · simp only [reverseEdge,hf,RhombusCell.halfTurn]
  · simp only [reverseEdge,he,RhombusCell.halfTurn]
  · rw [hu,hv]
    have hx : cross2 (-C.u) (-C.v)=cross2 C.u C.v := by simp [cross2]
    rw [hx]
    exact hpos

theorem positive_step_injective {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f g : OrientedEdge G} (hf : PositiveCellStep f e) (hg : PositiveCellStep g e) : f=g := by
  have h := positive_step_functional ht hf.reverse hg.reverse
  have hh := congrArg reverseEdge h
  simpa only [reverseEdge_involutive] using hh

theorem positive_path_reverse {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : Relation.ReflTransGen PositiveCellStep e f) :
    Relation.ReflTransGen PositiveCellStep (reverseEdge f) (reverseEdge e) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact (Relation.ReflTransGen.single h.reverse).trans ih

theorem exists_spine_end {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    ∃ f, Relation.ReflTransGen PositiveCellStep e f ∧ ¬ ∃ g, PositiveCellStep f g := by
  classical
  let S : Finset (OrientedEdge G) := Finset.univ.filter
    (Relation.ReflTransGen PositiveCellStep e)
  have hS : S.Nonempty := ⟨e, by simp [S,Relation.ReflTransGen.refl]⟩
  obtain ⟨f,hf,hmax⟩ := S.exists_max_image edgeHeight hS
  have href : Relation.ReflTransGen PositiveCellStep e f := (Finset.mem_filter.mp hf).2
  refine ⟨f,href,?_⟩
  rintro ⟨g,hg⟩
  have hgS : g ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,href.tail hg⟩
  exact (not_lt_of_ge (hmax g hgS)) hg.height_lt

theorem exists_spine_start {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    ∃ f, Relation.ReflTransGen PositiveCellStep f e ∧ ¬ ∃ g, PositiveCellStep g f := by
  obtain ⟨f,hf,hn⟩ := exists_spine_end (reverseEdge e)
  refine ⟨reverseEdge f,?_,?_⟩
  · simpa only [reverseEdge_involutive] using positive_path_reverse hf
  · rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact hn ⟨reverseEdge g,hh⟩

end Swanepoel
