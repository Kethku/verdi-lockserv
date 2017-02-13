Require Import Verdi.Verdi.

Require Import LockServSerialized.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlNatIntExt.

Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFin.

Extraction "extraction/lockserv/ocaml/LockServSerialized.ml" seq transformed_base_params transformed_multi_params.