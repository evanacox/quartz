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

//! # Quartz Prelude
//!
//! This prelude re-exports the essentials for working with Quartz. Most notably,
//! it re-exports almost all of the IR APIs, along with some of the simple compile APIs.
//!
//! More advanced cases will always need to import directly, this re-exported subset
//! is meant to be enough for simple tutorial/example programs to compile.

use crate::ir;

pub use ir::*;
