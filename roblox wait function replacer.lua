local function wait(num) -- great for rpm guns like local function rpm(num) to change it
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
