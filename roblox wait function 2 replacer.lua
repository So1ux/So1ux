local function wait(n)
	if not n then
		return game:GetService("RunService").Heartbeat:Wait()
	else
		local lasted = 0
		repeat
			lasted += game:GetService("RunService").Heartbeat:Wait()
		until lasted >= n
		return lasted
	end
end
