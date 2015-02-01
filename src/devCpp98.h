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
#ifndef _DEVCPP98_H_
#define _DEVCPP98_H_

#define CPP98

// new keywords (since C++11)
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

#define __auto_storage__	auto // until C++11 [auto -> __auto_type__ since C++11)

#define __delete_function__		// since C++11 (=delete)

#define __no_exception__	throw()
#define __throw1(e)			throw(e)
#define __throw2(e,f)		throw(e,f)
#define __throw3(e,f,g)		throw(e,f,g)
#define __throw4(e,f,g,h)	throw(e,f,g,h)
#define __throw5(e,f,g,h,i)	throw(e,f,g,h,i)

#define null NULL

#endif

