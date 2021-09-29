local function wait(num)
	if not num then
		return os.clock()
	else
		local current = 0
		local target = num*100000000000
		repeat 
			current += os.clock()
		until current >= target
		return current
	end
end
