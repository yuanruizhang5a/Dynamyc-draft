<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
Revise the current code in Rocq-copy/LPL. 

Current ``formula`` contains also non-primitive operators such as `Falsity`, `Disj`, `Impl`, `Ex`, `DualSuffix`, and `Diamond`. Redefine ``formula``, let it only contain primitive operators, and define other non-primitive ones according to primitive ones. 

Adjust other parts of the code to this change. 

After the revision, refine the whole code in Rocq-copy/LPL to improve its clarity and readability while preserving its original logic and functionality.