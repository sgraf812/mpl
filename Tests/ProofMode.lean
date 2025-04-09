import MPL
import MPL.ProofMode

open MPL

variable (σs : List Type)

theorem start_stop (Q : SProp σs) (H : Q ⊢ₛ Q) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sstop
  exact H

theorem exact (Q : SProp σs) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sexact HQ

theorem clear (P Q : SProp σs) : P ⊢ₛ Q → Q := by
  sintro HP
  sintro HQ
  sclear HP
  sexact HQ

theorem assumption (P Q : SProp σs) : Q ⊢ₛ P → Q := by
  sintro _ _
  sassumption
