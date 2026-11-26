module
public import Swanepoel.TerminalWalkIntegral
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.selectedWalkDisplacement_concat {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) {S : Finset (ContactEdge G)}
    {a b c : Fin n} (p : (G.contactGraph S).Walk a b) (h : (G.contactGraph S).Adj b c) :
    G.selectedWalkDisplacement A (p.concat h)=G.selectedWalkDisplacement A p+
      retainedDisplacement A ⟨(b,c),G.contactGraph_le S h⟩ := by
  rw [SimpleGraph.Walk.concat_eq_append,G.selectedWalkDisplacement_append]
  simp [PennyGraph.selectedWalkDisplacement]

theorem PennyGraph.selectedWalkDisplacement_reverse {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) {S : Finset (ContactEdge G)}
    {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    G.selectedWalkDisplacement A p.reverse= -G.selectedWalkDisplacement A p := by
  induction p with
  | nil => simp [PennyGraph.selectedWalkDisplacement]
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.reverse_cons,G.selectedWalkDisplacement_append,ih]
    have hd : retainedDisplacement A
        (⟨(b,a),G.contactGraph_le S h.symm⟩ : OrientedEdge G)=
        -retainedDisplacement A (⟨(a,b),G.contactGraph_le S h⟩ : OrientedEdge G) := by
      change trackDisplacement _ (reverseEdge (⟨(a,b),G.contactGraph_le S h⟩ : OrientedEdge G))= _
      exact trackDisplacement_reverse _ _
    simp only [PennyGraph.selectedWalkDisplacement]
    rw [hd]
    abel

theorem PennyGraph.selectedWalkDisplacement_eq_potential {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) (S : Finset (ContactEdge G)) (P : Fin n → Plane)
    (hP : ∀ {a b : Fin n} (h : (G.contactGraph S).Adj a b),
      P b-P a=retainedDisplacement A ⟨(a,b),G.contactGraph_le S h⟩)
    {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    G.selectedWalkDisplacement A p=P b-P a := by
  induction p with
  | nil => simp [PennyGraph.selectedWalkDisplacement]
  | @cons a b c h p ih =>
    rw [PennyGraph.selectedWalkDisplacement,← hP h,ih]
    abel

theorem PennyGraph.exists_displacement_potential_iff {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) (S : Finset (ContactEdge G))
    (hc : (G.contactGraph S).Connected) :
    (∃ P : Fin n → Plane, ∀ {a b : Fin n} (h : (G.contactGraph S).Adj a b),
      P b-P a=retainedDisplacement A ⟨(a,b),G.contactGraph_le S h⟩) ↔
    (∀ a : Fin n, ∀ p : (G.contactGraph S).Walk a a, G.selectedWalkDisplacement A p=0) := by
  constructor
  · rintro ⟨P,hP⟩ a p
    rw [G.selectedWalkDisplacement_eq_potential A S P hP p,sub_self]
  · intro hclosed
    obtain ⟨r⟩ := hc.nonempty
    let paths (v : Fin n) : (G.contactGraph S).Walk r v := Classical.choice (hc.preconnected r v)
    let P (v : Fin n) : Plane := G.selectedWalkDisplacement A (paths v)
    refine ⟨P,?_⟩
    intro a b h
    have hz := hclosed r (((paths a).concat h).append (paths b).reverse)
    rw [G.selectedWalkDisplacement_append,G.selectedWalkDisplacement_concat,
      G.selectedWalkDisplacement_reverse] at hz
    have heq : P a+retainedDisplacement A ⟨(a,b),G.contactGraph_le S h⟩=P b :=
      sub_eq_zero.mp hz
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using heq.symm

end Swanepoel
