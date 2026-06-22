--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 47) then
					if (Enum <= 23) then
						if (Enum <= 11) then
							if (Enum <= 5) then
								if (Enum <= 2) then
									if (Enum <= 0) then
										Env[Inst[3]] = Stk[Inst[2]];
									elseif (Enum == 1) then
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									end
								elseif (Enum <= 3) then
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								elseif (Enum > 4) then
									if (Stk[Inst[2]] <= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 8) then
								if (Enum <= 6) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum > 7) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 9) then
								Stk[Inst[2]] = {};
							elseif (Enum > 10) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 17) then
							if (Enum <= 14) then
								if (Enum <= 12) then
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								elseif (Enum == 13) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								end
							elseif (Enum <= 15) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum > 16) then
								do
									return;
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 20) then
							if (Enum <= 18) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum == 19) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 21) then
							VIP = Inst[3];
						elseif (Enum == 22) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 35) then
						if (Enum <= 29) then
							if (Enum <= 26) then
								if (Enum <= 24) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								elseif (Enum > 25) then
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 44) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								elseif (Stk[Inst[2]] <= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 27) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							elseif (Enum == 28) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							end
						elseif (Enum <= 32) then
							if (Enum <= 30) then
								do
									return Stk[Inst[2]];
								end
							elseif (Enum == 31) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 33) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						elseif (Enum > 34) then
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 41) then
						if (Enum <= 38) then
							if (Enum <= 36) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 37) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 39) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						elseif (Enum == 40) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 44) then
						if (Enum <= 42) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 43) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 45) then
						Stk[Inst[2]]();
					elseif (Enum == 46) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 71) then
					if (Enum <= 59) then
						if (Enum <= 53) then
							if (Enum <= 50) then
								if (Enum <= 48) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum > 49) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum <= 51) then
								Stk[Inst[2]] = {};
							elseif (Enum > 52) then
								Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
							else
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum <= 56) then
							if (Enum <= 54) then
								Env[Inst[3]] = Stk[Inst[2]];
							elseif (Enum == 55) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 57) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						elseif (Enum > 58) then
							Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 65) then
						if (Enum <= 62) then
							if (Enum <= 60) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum > 61) then
								Stk[Inst[2]]();
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 63) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						elseif (Enum == 64) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 68) then
						if (Enum <= 66) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 67) then
							Stk[Inst[2]] = Inst[3];
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 69) then
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 44) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					elseif (Enum == 70) then
						do
							return Stk[Inst[2]];
						end
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 83) then
					if (Enum <= 77) then
						if (Enum <= 74) then
							if (Enum <= 72) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							elseif (Enum > 73) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
							end
						elseif (Enum <= 75) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						elseif (Enum > 76) then
							local A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								local VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 80) then
						if (Enum <= 78) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 79) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 81) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					elseif (Enum == 82) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 89) then
					if (Enum <= 86) then
						if (Enum <= 84) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Enum > 85) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 87) then
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 88) then
						do
							return;
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					end
				elseif (Enum <= 92) then
					if (Enum <= 90) then
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
					elseif (Enum == 91) then
						Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
					else
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 93) then
					local A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
				elseif (Enum > 94) then
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
				else
					local A = Inst[2];
					Top = (A + Varargsz) - 1;
					for Idx = A, Top do
						local VA = Vararg[Idx - A];
						Stk[Idx] = VA;
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!353Q0003043Q0067616D65030A3Q004765745365727669636503133Q004C6F63616C53746F7261676553657276696365030A3Q0052756E5365727669636503023Q006F7303053Q00636C6F636B03073Q0044726177696E672Q033Q006E6577030D3Q00576F726C64546F5363722Q656E03093Q00776F726B737061636503053Q00576F726C64030B3Q00496E74657261637469766503073Q00506C6179657273030B3Q004C6F63616C506C61796572030C3Q0057616974466F724368696C6403093Q00506C6179657247756903093Q005363722Q656E47756903063Q0043656E74657203063Q004D692Q646C6503103Q004861636B696E674D696E6967616D657303083Q0041544D204861636B03053Q00466F6E747303063Q0053797374656D03073Q0076697369626C65025Q00B49640030A3Q0054657874436F6C6F7233025Q00A0AC4003073Q0061746D5465787403043Q0053697A65026Q003E4003043Q00466F6E7403053Q00436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742026Q003C40026Q005F40028Q0003073Q004F75746C696E652Q0103043Q0061746D7303083Q0064726177696E677303073Q0067657466656E762Q033Q00465053026Q005E4003063Q006C6F6164554903063Q00412Q6445535003083Q00746F6E756D626572026Q00F03F030D3Q0052656E6465725374652Q70656403073Q00436F2Q6E65637403043Q007461736B03043Q007761697403053Q007061697273007C4Q00097Q001207000100013Q00200D000100010002001243000300034Q0038000100030002001207000200013Q00200D000200020002001243000400044Q0038000200040002001207000300053Q00204F000300030006001207000400073Q00204F000400040008001207000500093Q0012070006000A3Q00204F00070006000B00204F00070007000C001207000800013Q00200D000800080002001243000A000D4Q00380008000A000200204F00090008000E00200D000A0009000F001243000C00104Q0038000A000C000200204F000B000A001100204F000B000B001200204F000B000B001300204F000B000B001400204F000C000B0015001207000D00073Q00204F000D000D001600204F000D000D00172Q0009000E6Q0009000F3Q0002003050000F00180019003050000F001A001B2Q000900106Q000900113Q00040030500011001D001E0010080011001F000D001207001200213Q00204F001200120022001243001300233Q001243001400243Q001243001500254Q00380012001500020010080011002000120030500011002600270010080010001C00112Q000900115Q001008000E002800112Q000900115Q001008000E002900110012070011002A4Q00550011000100020030500011002B002C00061A00113Q000100012Q002C3Q000F3Q00061A00120001000100012Q002C3Q000F3Q00061A00130002000100022Q002C3Q000E4Q002C3Q00043Q00061A00140003000100022Q002C3Q000E4Q002C3Q00054Q005400155Q00061A00160004000100032Q002C3Q00154Q002C3Q000C4Q002C3Q00123Q00061A00170005000100052Q002C3Q00144Q002C3Q00114Q002C3Q000B4Q002C3Q00164Q002C3Q00153Q000232001800063Q00061A00190007000100012Q002C3Q00183Q00061A001A0008000100012Q002C3Q00063Q00122Q001A002D3Q00061A001A0009000100022Q002C3Q00184Q002C3Q00133Q00122Q001A002E3Q00061A001A000A000100022Q002C3Q00074Q002C3Q00103Q000232001B000B3Q001207001C002F3Q001207001D002A4Q0055001D0001000200204F001D001D002B2Q005D001C0002000200105B001C0030001C001207001D00053Q00204F001D001D00062Q0055001D0001000200204F001E0002003100200D001E001E003200061A0020000C000100052Q002C3Q00034Q002C3Q001D4Q002C3Q001C4Q002C3Q001B4Q002C3Q00174Q0053001E00200001001207001E002D4Q003E001E00010001001207001E00333Q00204F001E001E0034001243001F00304Q005C001E00020001001207001E00353Q00204F001F000E00292Q004C001E000200200004293Q00780001000623001E0078000100020004293Q007800010004293Q007000012Q00593Q00013Q000D3Q00053Q0003073Q00412Q6472652Q73030B3Q006D656D6F72795F7265616403043Q006279746503073Q0076697369626C65028Q00010D3Q00204F00013Q0001001207000200023Q001243000300034Q002000045Q00204F0004000400042Q00510004000100042Q00380002000400020026570002000A000100050004293Q000A00012Q005A00036Q0054000300014Q001E000300024Q00593Q00017Q00093Q0003073Q00412Q6472652Q73030A3Q0054657874436F6C6F7233030B3Q006D656D6F72795F7265616403053Q00666C6F6174026Q001040026Q00204003013Q005203013Q004703013Q004201163Q00204F00013Q00012Q002000025Q00204F0002000200022Q0051000100010002001207000200033Q001243000300044Q0026000400014Q0038000200040002001207000300033Q001243000400043Q00200E0005000100052Q0038000300050002001207000400033Q001243000500043Q00200E0006000100062Q00380004000600022Q000900053Q00030010080005000700020010080005000800030010080005000900042Q001E000500024Q00593Q00017Q00073Q0003083Q0064726177696E677303043Q005465787403083Q00506F736974696F6E03053Q00706169727303023Q00696403073Q00747261636B657203053Q006C6162656C06294Q002000065Q00204F0006000600012Q0012000600063Q00064E00060020000100010004293Q002000012Q0020000600013Q001243000700024Q005D00060002000200100800060002000200064A0004000E00013Q0004293Q000E000100204F00070001000300064E0007000F000100010004293Q000F00012Q0026000700013Q00064A0005001800013Q0004293Q00180001001207000800044Q0026000900054Q004C00080002000A0004293Q001600012Q001B0006000B000C00062300080015000100020004293Q001500012Q002000085Q00204F0008000800012Q000900093Q00030010080009000500030010080009000600070010080009000700062Q001B00083Q00090004293Q002400012Q002000065Q00204F0006000600012Q0012000600064Q001E000600024Q002000065Q00204F0006000600012Q0012000600064Q001E000600024Q00593Q00017Q00083Q0003053Q00706169727303083Q0064726177696E677303073Q00747261636B657203083Q00506F736974696F6E03053Q006C6162656C03073Q0056697369626C653Q012Q001C3Q0012073Q00014Q002000015Q00204F0001000100022Q004C3Q000200020004293Q0019000100204F00050004000300064A0005000D00013Q0004293Q000D000100204F00050004000300204F00050005000400064E0005000D000100010004293Q000D000100204F0005000400032Q0020000600014Q0026000700054Q004C00060002000700064A0007001700013Q0004293Q0017000100204F00080004000500100800080004000600204F0008000400050030500008000600070004293Q0019000100204F0008000400050030500008000600080006233Q0005000100020004293Q000500012Q00593Q00017Q001F3Q00010003043Q007761726E030C3Q006D696E6967616D652061746D03043Q007461736B03043Q0077616974027Q004003093Q0053657175656E63653203043Q005465787403063Q00737472696E6703053Q0073706C697403013Q0020026Q00F03F026Q00084003043Q004C69737403013Q003103053Q007061697273030B3Q004765744368696C6472656E030E3Q0046696E6446697273744368696C6403093Q00546578744C6162656C03053Q007072696E74030B3Q0047657446752Q6C4E616D6503053Q00666F756E6403013Q0047026Q66D63F03043Q006D6174682Q033Q00616273027B14AE47E17A943F030B3Q006D6F757365317072652Q73030D3Q006D6F7573653172656C6561736503053Q00636C69636B2Q01006F4Q00593Q00014Q00207Q0026573Q006E000100010004293Q006E00010012073Q00023Q001243000100034Q005C3Q000200012Q00543Q00014Q003F7Q0012073Q00043Q00204F5Q0005001243000100064Q005C3Q000200012Q00203Q00013Q00204F5Q000700204F5Q0008001207000100093Q00204F00010001000A2Q002600025Q0012430003000B4Q00380001000300022Q00263Q00013Q00204F00013Q000C00204F00023Q000600204F00033Q000D2Q0020000400013Q00204F00040004000E00204F00040004000F2Q005400056Q0001000600063Q001207000700024Q0026000800014Q0026000900024Q0026000A00034Q00530007000A0001001207000700103Q00200D0008000400112Q003C000800094Q002A00073Q00090004293Q003D000100200D000C000B0012001243000E00134Q0038000C000E000200064A000C003D00013Q0004293Q003D000100204F000D000C0008000610000D003D000100010004293Q003D0001001207000D00144Q0020000E00024Q0026000F000C4Q003C000E000F4Q0016000D3Q00012Q00260006000B3Q001207000D00143Q00200D000E000B00152Q003C000E000F4Q0016000D3Q0001001207000D00143Q001243000E00164Q005C000D0002000100062300070028000100020004293Q00280001001207000700043Q00204F0007000700052Q003E000700010001001207000700103Q00200D0008000400112Q003C000800094Q002A00073Q00090004293Q006A000100200D000C000B0012001243000E00134Q0038000C000E000200064A000C006A00013Q0004293Q006A000100204F000D000C0008000610000D006A000100010004293Q006A00012Q0020000D00024Q0026000E000C4Q005D000D00020002001207000E00144Q0026000F000D4Q005C000E0002000100204F000E000D0017001049000E0018000E001207000F00193Q00204F000F000F001A2Q00260010000E4Q005D000F000200022Q0026000E000F3Q002619000E006A0001001B0004293Q006A0001001207000F001C4Q003E000F00010001001207000F00043Q00204F000F000F00052Q003E000F00010001001207000F001D4Q003E000F00010001001207000F00023Q0012430010001E3Q00204F0011000C00082Q0053000F001100012Q0054000500013Q00062300070047000100020004293Q004700010026570005003F0001001F0004293Q003F00012Q00593Q00017Q00013Q003Q010D4Q002000016Q003E0001000100012Q0020000100014Q0020000200024Q005D0001000200020026570001000A000100010004293Q000A00012Q0020000200034Q003E0002000100010004293Q000C00012Q005400026Q003F000200044Q00593Q00017Q00073Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q00426173655061727403083Q00506F736974696F6E03043Q0053697A6503063Q00434672616D65011B3Q00064A3Q001800013Q0004293Q00180001001207000100013Q00200D00023Q00022Q003C000200034Q002A00013Q00030004293Q0016000100200D000600050003001243000800044Q003800060008000200064A0006001600013Q0004293Q0016000100204F00060005000500064A0006001600013Q0004293Q0016000100204F00060005000600064A0006001600013Q0004293Q0016000100204F00060005000700064A0006001600013Q0004293Q001600012Q001E000500023Q00062300010007000100020004293Q000700012Q0001000100014Q001E000100024Q00593Q00017Q00043Q00026Q00F03F03043Q007461736B03043Q007761697403063Q00412Q6445535000134Q000900016Q004D00026Q000B00013Q000100204F000200010001001207000300023Q00204F000300030003001243000400014Q005C0003000200012Q002000036Q0026000400024Q005D00030002000200064A0003000400013Q0004293Q00040001001207000400044Q004D00056Q001600043Q00010004293Q001200010004293Q000400012Q00593Q00017Q00033Q0003023Q00554903063Q00412Q64546162030A3Q0053616E2041756472656100073Q0012073Q00013Q00204F5Q0002001243000100033Q00061A00023Q000100012Q002B8Q00533Q000200012Q00593Q00013Q00013Q00093Q0003073Q0053656374696F6E030F3Q005175616C697479206F66206C69666503043Q004C65667403063Q0042752Q746F6E03183Q00627970612Q73206D696E6967616D6573202F206861636B7303163Q00466173742050726F78696D6974792050726F6D70747303063Q00546F2Q676C65030F3Q0077616E746564457370546F2Q676C65030A3Q0057616E7465642045535001123Q00200D00013Q0001001243000300023Q001243000400034Q003800010004000200200D000200010004001243000400053Q00023200056Q005300020005000100200D000200010004001243000400063Q00061A00050001000100012Q002B8Q005300020005000100200D000200010007001243000400083Q001243000500094Q00530002000500012Q00593Q00013Q00023Q00083Q0003053Q00676574676303103Q0064697361626C654D696E6967616D6573030E3Q0064697361626C654861636B696E6703053Q007061697273030C3Q006D656D6F72795F777269746503043Q006279746503043Q00612Q6472026Q00F03F00123Q0012073Q00014Q0009000100023Q001243000200023Q001243000300034Q00390001000200012Q005D3Q00020002001207000100044Q002600026Q004C0001000200030004293Q000F0001001207000600053Q001243000700063Q00204F000800050007001243000900084Q00530006000900010006230001000A000100020004293Q000A00012Q00593Q00017Q000C3Q00025Q0080734003053Q007061697273030E3Q0047657444657363656E64616E7473025Q00407F40028Q0003043Q007461736B03043Q007761697403093Q00436C612Q734E616D65030F3Q0050726F78696D69747950726F6D707403073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503063Q00646F75626C6500193Q0012433Q00013Q001207000100024Q002000025Q00200D0002000200032Q003C000200034Q002A00013Q00030004293Q0016000100200C0006000400040026570006000D000100050004293Q000D0001001207000600063Q00204F0006000600072Q003E00060001000100204F00060005000800265700060016000100090004293Q0016000100204F00060005000A0012070007000B3Q0012430008000C4Q0051000900063Q001243000A00054Q00530007000A000100062300010007000100020004293Q000700012Q00593Q00017Q00013Q0003073Q00412Q6472652Q7306124Q002000066Q002600076Q005D00060002000200064A0006000F00013Q0004293Q000F00012Q0020000700013Q00204F00083Q00012Q0026000900064Q0026000A00014Q0026000B00024Q0026000C00034Q0026000D00054Q00380007000D00022Q001E000700023Q0004293Q000F00012Q0001000700074Q001E000700024Q00593Q00017Q00073Q0003053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D652Q033Q0041544D03063Q00412Q6445535003043Q005F41544D03073Q0061746D5465787400153Q0012073Q00014Q002000015Q00200D0001000100022Q003C000100024Q002A5Q00020004293Q0012000100204F00050004000300265700050012000100040004293Q00120001001207000500054Q0026000600043Q001243000700043Q001243000800064Q0054000900014Q0054000A00014Q0020000B00013Q00204F000B000B00072Q00530005000B00010006233Q0006000100020004293Q000600012Q00593Q00019Q003Q00014Q00593Q00017Q00023Q0003043Q007461736B03053Q00737061776E01104Q002000016Q00550001000100022Q0020000200014Q00560002000100022Q0020000300023Q0006240003000F000100020004293Q000F00012Q003F000100014Q0020000200034Q003E000200010001001207000200013Q00204F0002000200022Q0020000300044Q002600046Q00530002000400012Q00593Q00017Q00", GetFEnv(), ...);
