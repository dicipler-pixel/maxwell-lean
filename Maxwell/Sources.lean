/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/

/-!
# Source records: Maxwell's claims, hypotheses, and stated limits, in his words

Each record names the work, edition, article or section, page in the edition used, the
Internet Archive identifier of the scan it was checked against, an exact quotation (checked
against that scan), and a status. These are **data**, not theorems: nothing here is asserted
in Lean. They exist so that the limits Maxwell stated stay visible next to the proofs and
cannot be silently upgraded.

Quotes are taken from those scans with line-break artefacts (and obvious single-character
OCR typographical errors, such as "ass unfruitful") corrected against the readable wording.
Formulae that the OCR left illegible are not invented here.
-/

namespace Maxwell

/-- How a passage is used in this library. -/
inductive Status
  /-- A claim Maxwell makes, whether proved here, stated in `Statements`, or physical. -/
  | claim
  /-- A hypothesis Maxwell introduces or adopts (it is a hypothesis in Lean too). -/
  | hypothesis
  /-- A limit Maxwell states on his own theory. Never formalized as proved. -/
  | statedLimit
  /-- An empirical position Maxwell takes. -/
  | empirical
  /-- A model Maxwell himself calls provisional. -/
  | provisional
  deriving DecidableEq, Repr

/-- A citation to Maxwell's text. -/
structure Source where
  work : String
  edition : String
  locus : String
  page : String
  localFile : String
  quote : String
  status : Status
  deriving Repr

def treatise1873I : String := "electricandmagne01maxwrich"
def treatise1873II : String := "electricandmagne02maxwrich"
def treatise1881I : String := "treatiseonelectr01maxwrich"
def sciPapersI : String := "scientificpapers01maxwuoft"

def art107 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. I"
    locus := "Art. 107", page := "p. 127", localFile := treatise1873I
    quote := "By establishing the necessity of assuming these internal forces in the theory of an \
electric medium, we have advanced a step in that theory which will not be lost though we should \
fail in accounting for these internal forces, or in explaining the mechanism by which they can be \
maintained in air, glass, and other dielectric media."
    status := .claim }

def art107_illustration : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. I"
    locus := "Art. 107", page := "p. 128", localFile := treatise1873I
    quote := "This illustration is to be taken merely as an explanation of what is meant by the \
tension and pressure, not as a physical theory to account for them."
    status := .statedLimit }

def art110 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. I"
    locus := "Art. 110", page := "p. 132", localFile := treatise1873I
    quote := "It must be carefully borne in mind that we have made only one step in the theory of \
the action of the medium. We have supposed it to be in a state of stress, but we have not in any \
way accounted for this stress, or explained how it is maintained."
    status := .statedLimit }

def art111 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. I"
    locus := "Art. 111", page := "p. 132", localFile := treatise1873I
    quote := "I have not been able to make the next step, namely, to account by mechanical \
considerations for these stresses in the dielectric. I therefore leave the theory at this point, \
merely stating what are the other parts of the phenomenon of induction in dielectrics."
    status := .statedLimit }

/-- Location of electrostatic energy, its equality with the tension, and the printed formula of
p. 134. The displayed equation was read from the 1873 vol. I page scan, p. 134 (Internet Archive
`electricandmagne01maxwrich`), not from the garbled OCR: italic `p` and Fraktur `𝔇`, `𝔈`. -/
def art111_energy : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. I"
    locus := "Art. 111", page := "p. 134", localFile := treatise1873I
    quote := "A dielectric medium, when thus polarized, is the seat of electrical energy, and the \
energy in unit of volume of the medium is numerically equal to the electric tension on unit of \
area, both quantities being equal to half the product of the displacement and the resultant \
electromotive force, or p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇², where p is the electric tension, \
𝔇 the displacement, 𝔈 the electromotive force, and K the specific inductive capacity"
    status := .claim }

/-- 1881 Art. 105: the stress components have physical significance only if the action is through
the medium. Cited on `stress1881`. -/
def art105_1881 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "2nd ed., Clarendon 1881, vol. I"
    locus := "Art. 105", page := "p. 147", localFile := treatise1881I
    quote := "If the action of the system E2 on E1 does in reality take place by direct action at \
a distance, without the intervention of any medium, we must consider the quantities pxx &c. as \
mere abbreviated forms for certain symbolical expressions, and as having no physical significance."
    status := .hypothesis }

def art645 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 645 (see also Art. 832)", page := "pp. 257–258", localFile := treatise1873II
    quote := "We have asserted nothing as yet with respect to the mode in which this state of \
stress is originated and maintained in the medium. ... Any further explanation of the state of \
stress, by means of the motion of the medium or otherwise, must be regarded as a separate and \
independent part of the theory, which may stand or fall without affecting our present position. \
See Art. 832. In the first part of this treatise, Art. 108, we shewed that the observed \
electrostatic forces may be conceived as operating through the intervention of a state of \
stress in the surrounding medium. We have now done the same for the electromagnetic forces, \
and it remains to be seen whether the conception of a medium capable of supporting these \
states of stress is consistent with other known phenomena, or whether we shall have to put it aside as unfruitful."
    status := .statedLimit }

def art645_superposition : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 645", page := "p. 258", localFile := treatise1873II
    quote := "In a field in which electrostatic as well as electromagnetic action is taking place, \
we must suppose the electrostatic stress described in Part I to be superposed on the \
electromagnetic stress which we have been considering."
    status := .hypothesis }

def art644 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 644", page := "p. 257", localFile := treatise1873II
    quote := "If we adopt the theories of Ampere and Weber as to the nature of magnetic and \
diamagnetic bodies, and assume that magnetic and diamagnetic polarity are due to molecular \
electric currents, we get rid of imaginary magnetic matter, and find that everywhere m = 0"
    status := .hypothesis }

def art636 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 636", page := "p. 249", localFile := treatise1873II
    quote := "According to our hypothesis, we assume the kinetic energy to exist wherever there is \
magnetic force, that is, in general, in every part of the field. The amount of this energy per \
unit of volume is -(1/8π) S.𝔅ℌ, and this energy exists in the form of some kind of motion of the \
matter in every portion of space."
    status := .hypothesis }

/-- Equal totals under a supposition, not a location claim. Location of the energy is stated
literally in 1865 § 74, as a hypothesis in Art. 636, and in 1873 Art. 111 ("is the seat of
electrical energy"). -/
def art631 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 631", page := "p. 247", localFile := treatise1873II
    quote := "Hence, the electrostatic energy of the whole field will be the same if we suppose \
that it resides in every part of the field where electrical force and electrical displacement \
occur, instead of being confined to the places where free electricity is found."
    status := .claim }

/-- § 73 restricts the mechanical language of the paper; the literal location claim is § 74. -/
def dyn1865_s73 : Source :=
  { work := "A Dynamical Theory of the Electromagnetic Field (Phil. Trans. 155, 1865)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXV"
    locus := "§ 73", page := "p. 564", localFile := sciPapersI
    quote := "All such phrases in the present paper are to be considered as illustrative, not as \
explanatory."
    status := .statedLimit }

/-- Location is stated literally; "the motion and the strain of one and the same medium" is
his "very probable hypothesis". -/
def dyn1865_s74 : Source :=
  { work := "A Dynamical Theory of the Electromagnetic Field (Phil. Trans. 155, 1865)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXV"
    locus := "§ 74", page := "p. 564", localFile := sciPapersI
    quote := "In speaking of the Energy of the field, however, I wish to be understood literally. \
All energy is the same as mechanical energy, whether it exists in the form of motion or in that \
of elasticity, or in any other form. The energy in electromagnetic phenomena is mechanical \
energy. The only question is, Where does it reside? On the old theories it resides in the \
electrified bodies, conducting circuits, and magnets, in the form of an unknown quality called \
potential energy, or the power of producing certain effects at a distance. On our theory it \
resides in the electromagnetic field, in the space surrounding the electrified and magnetic \
bodies, as well as in those bodies themselves, and is in two different forms, which may be \
described without hypothesis as magnetic polarization and electric polarization, or, according to \
a very probable hypothesis, as the motion and the strain of one and the same medium."
    status := .claim }

def dyn1865_s82 : Source :=
  { work := "A Dynamical Theory of the Electromagnetic Field (Phil. Trans. 155, 1865)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXV"
    locus := "§ 82 (note on the attraction of gravitation)", page := "pp. 570–571"
    localFile := sciPapersI
    quote := "As I am unable to understand in what way a medium can possess such properties, I \
cannot go any further in this direction in searching for the cause of gravitation."
    status := .statedLimit }

def art866 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 866", page := "pp. 437–438", localFile := treatise1873II
    quote := "In fact, whenever energy is transmitted from one body to another in time, there must \
be a medium or substance in which the energy exists after it leaves one body and before it \
reaches the other"
    status := .claim }

def art549 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 549", page := "p. 181", localFile := treatise1873II
    quote := "These results shew clearly that, if the phenomena are due to momentum, the momentum \
is certainly not that of the electricity in the wire, because the same wire, conveying the same \
current, exhibits effects which differ according to its form; and even when its form remains the \
same, the presence of other bodies, such as a piece of iron or a closed metallic circuit, affects \
the result."
    status := .claim }

def art574_575 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Arts. 574–575", page := "pp. 200–202", localFile := treatise1873II
    quote := "As it is of great importance to determine whether any part of the kinetic energy is \
of the form T_me, consisting of products of ordinary velocities and strengths of electric \
currents, it is desirable that experiments should be made on this subject with great care. ... \
No phenomenon of this kind has yet been observed."
    status := .empirical }

/-- A second empirical record from the same discussion: Maxwell will not assume a material
current. The quoted sentence sits on p. 202, still in Art. 574 (the paragraph begins at the
end of p. 201, "It appears to me, however…"). Art. 575 begins later on p. 202 ("575.] The
experimental investigation of the second term…"); the running head "[575." names that later
article, not this paragraph. -/
def art574_current : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 574", page := "pp. 201–202", localFile := treatise1873II
    quote := "there is, as yet, no experimental evidence to shew whether the electric current is \
really a current of a material substance, or a double current, or whether its velocity is great \
or small as measured in feet per second."
    status := .empirical }

def art590 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 590", page := "p. 214", localFile := treatise1873II
    quote := "The vector 𝔄 represents in direction and magnitude the time-integral of the \
electromotive force which a particle placed at the point (x, y, z) would experience if the \
primary current were suddenly stopped. We shall therefore call it the Electrokinetic Momentum \
at the point (x, y, z). It is identical with the quantity which we investigated in Art. 405 \
under the name of the vector-potential of magnetic induction."
    status := .claim }

def dyn1865_s57_58 : Source :=
  { work := "A Dynamical Theory of the Electromagnetic Field (Phil. Trans. 155, 1865)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXV"
    locus := "§§ 57–58", page := "pp. 555–556", localFile := sciPapersI
    quote := "(57) Let F, G, H represent the components of electromagnetic momentum at any point \
of the field, due to any system of magnets or currents. ... (58) ... if we integrate round the \
circuit, we shall get the total electromagnetic momentum of the circuit, or the number of lines \
of magnetic force which pass through it"
    status := .claim }

def art616 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 616", page := "p. 235", localFile := treatise1873II
    quote := "The quantity χ disappears from the equations (A), and it is not related to any \
physical phenomenon. If we suppose it to be zero everywhere, J will also be zero everywhere"
    status := .hypothesis }

def art377 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 377", page := "p. 4", localFile := treatise1873II
    quote := "In every Magnet the total quantity of Magnetism (reckoned algebraically) is zero."
    status := .empirical }

def art832 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 832", page := "p. 418", localFile := treatise1873II
    quote := "magnetization is a phenomenon, not of large masses of iron, but of molecules, that \
is to say, of portions of the substance so small that we cannot by any mechanical method cut one \
of them in two, so as to obtain a north pole separate from a south pole."
    status := .empirical }

def physicalLines1861_provisional : Source :=
  { work := "On Physical Lines of Force (Phil. Mag. 1861–62)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXIII"
    locus := "Part II", page := "p. 486", localFile := sciPapersI
    quote := "any one who understands the provisional and temporary character of this hypothesis"
    status := .provisional }

/-- All records, for review. -/
def allSources : List Source :=
  [art107, art107_illustration, art110, art111, art111_energy, art105_1881, art645,
    art645_superposition, art644, art636, art631, dyn1865_s73, dyn1865_s74, dyn1865_s82, art866,
    art549, art574_575, art574_current, art590, dyn1865_s57_58, art616, art377, art832,
    physicalLines1861_provisional]

end Maxwell
