/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
#ifndef _DEVCPP11_H_
#define _DEVCPP11_H_

#define CPP11

// new keywords in C++11
// alignas
// alignof
// char16_t
// char32_t
// constexpr
// decltype
// default	(for compiler default constructions of constructor, destructor, etc)
// export	(for templates)
// static_assert
// thread_local

#define __auto_storage__		// until C++11
#define __auto_type__		auto // since C++11

#define __delete_function__	=delete

#define __no_exception__	noexcept
#define __throw1(e)			noexcept(false)
#define __throw2(e,f)		noexcept(false)
#define __throw3(e,f,g)		noexcept(false)
#define __throw4(e,f,g,h)	noexcept(false)
#define __throw5(e,f,g,h,i)	noexcept(false)

#define null nullptr

#endif
