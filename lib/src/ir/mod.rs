//======---------------------------------------------------------------======//
// Copyright (c) 2022 Evan Cox <evanacox00@gmail.com>.                       //
//                                                                           //
// Licensed under the Apache License, Version 2.0 (the "License");           //
// you may not use this file except in compliance with the License.          //
// You may obtain a copy of the License at                                   //
//                                                                           //
//     http://www.apache.org/licenses/LICENSE-2.0                            //
//                                                                           //
// Unless required by applicable law or agreed to in writing, software       //
// distributed under the License is distributed on an "AS IS" BASIS,         //
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  //
// See the License for the specific language governing permissions and       //
// limitations under the License.                                            //
//======---------------------------------------------------------------======//

//! # Quartz IR
//!
//! This module contains the data structures and functions that make up the
//! QIR API. All IR is modeled in this module and this module alone.
//!
//! This module also exposes the IR parsing/serialization APIs, as those are
//! closely intertwined with the structure of the IR.
//!
//! In memory, instructions are modeled using a doubly-linked list. This is due to
//! the nature of an IR designed specifically for optimizations:
//!
//! * The data structure must be able to maintain an order (i.e. it has to be sequential)
//! * The data structure must support fast random insertion/deletion
//! * The data structure **must support fast splicing**
//!
//! This effectively removes any possibility for clever data structures.

mod types;

pub use types::*;
