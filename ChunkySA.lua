script_name("ChunkySA")
local script_version = 1.90

local samp = require 'samp.events'
local imgui = require 'mimgui'
local encoding = require 'encoding'
local vkeys = require 'vkeys'
local dlstatus = require('moonloader').download_status
local lfs = require 'lfs'
local bit = require 'bit'
local os = require 'os'
local io = require 'io'

encoding.default = 'CP1251'
local u8 = encoding.UTF8

math.randomseed(os.time() + math.floor(os.clock() * 1000))

local mainFolder = getWorkingDirectory() .. '\\config\\ChunkySA\\'
local serversFolder = mainFolder .. 'servers\\'
local cacheFolder = mainFolder .. 'cache\\'
local settingsFile = mainFolder .. 'settings.json'

pcall(lfs.mkdir, mainFolder)
pcall(lfs.mkdir, serversFolder)
pcall(lfs.mkdir, cacheFolder)

local updateUrl = "https://raw.githubusercontent.com/kaip0v/ChunkySA/main/update.json"

local SIZE_LARGE = 10.0
local SIZE_SMALL = 3.0
local VERIFY_RADIUS = 45.0
local VERIFY_RADIUS_SQ = VERIFY_RADIUS * VERIFY_RADIUS
local COL_RADIUS = 100.0
local COL_RADIUS_SQ = COL_RADIUS * COL_RADIUS
local HYSTERESIS_MARGIN = 35.0
local CHUNK_SIZE = 100.0
local MAX_SAMP_SLOTS = 800

local presets = {
    { name = u8"Малая дистанция", maxObj = 500, speed = 150, dL = 500.0, dM = 300.0, dS = 160.0 },
    { name = u8"Средняя дистанция", maxObj = 800, speed = 300, dL = 800.0, dM = 450.0, dS = 250.0 },
    { name = u8"Дальняя дистанция", maxObj = 1500, speed = 600, dL = 1200.0, dM = 700.0, dS = 400.0 }
}

local cfg = {
    enabled = true,
    recordMapping = true,
    autoDeleteMissing = true,
    prioritizeLarge = true,
    disableFarCollision = true,
    autoUpdate = true,
    notifPos = 3,
    maxLocalObjects = 800,
    spawnSpeed = 300,
    distLarge = 800.0,
    distMedium = 450.0,
    distSmall = 250.0
}

local notifPositions = {
    u8"Слева снизу",
    u8"Снизу (по центру)",
    u8"Справа снизу",
    u8"Сверху (по центру)"
}

local UI = {
    windowState = imgui.new.bool(false),
    confirmClearTimer = 0,
    maxObjBuf = imgui.new.int[1](800)
}

local Sys = {
    tempSysNotifText = nil,
    tempSysNotifTimer = 0,
    tempSysNotifType = 0,
    wasTypingEscape = false
}

local activeTempFiles = {}
local modelSizeCache = {}
local currentServerKey = "offline"
local currentServerDisplay = "Offline"
local serverObjects = {}
local spatialGrid = {}
local spawnedLocal = {}
local localSampById = {}
local usedSampCount = 0
local nextSlotCursor = 999
local serverStreamedById = {}
local serverStreamedByHash = {}
local blockedServerIds = {}
local dynamicBlacklist = {}
local spawnQueue = {}
local spawnQueueHead = 1
local deferredMatQueue = {}
local isInternalEmul = false
local forceStreamTick = false
local spawnBudget = 0.0

local inInteriorWorld = false
local lastTeleportTime = 0
local lastServerCreateTime = 0

local stats = {
    totalCached = 0,
    renderedNow = 0,
    serverNow = 0,
    totalNow = 0,
    autoRemoved = 0
}

local dbDirty = false
local lastSaveTime = 0
local lastSpawnedClock = 0

local function file_exists(name)
    local f = io.open(name, "r")
    if f ~= nil then io.close(f) return true else return false end
end

local function showSystemNotification(text, nType)
    Sys.tempSysNotifText = text
    Sys.tempSysNotifType = nType or 0
    Sys.tempSysNotifTimer = os.clock() + 3.0
end

local function save_json(path, data)
    local file = io.open(path, "wb")
    if not file then return end
    local chunks = { "return " }
    local n = 1
    local function serialize(tbl)
        n = n + 1
        chunks[n] = "{"
        for k, v in pairs(tbl) do
            local key = type(k) == "string" and string.format("[%q]=", k) or ("[" .. tostring(k) .. "]=")
            local vt = type(v)
            if vt == "table" then
                n = n + 1
                chunks[n] = key
                serialize(v)
                n = n + 1
                chunks[n] = ","
            elseif vt == "string" then
                n = n + 1
                chunks[n] = key .. string.format("%q,", v)
            elseif vt == "number" or vt == "boolean" then
                n = n + 1
                chunks[n] = key .. tostring(v) .. ","
            end
        end
        n = n + 1
        chunks[n] = "}"
    end
    serialize(data)
    file:write(table.concat(chunks))
    file:close()
end

local function load_json(path)
    local file = io.open(path, "rb")
    if not file then return nil end
    local content = file:read("*a")
    file:close()
    if content == nil or content:gsub("%s", "") == "" then return {} end
    local ok, res = pcall(decodeJson, content)
    if ok and type(res) == "table" then return res end
    local func = load(content)
    if func then
        local ok2, res2 = pcall(func)
        if ok2 and type(res2) == "table" then return res2 end
    end
    return nil
end

local function saveSettings()
    save_json(settingsFile, cfg)
end

local function roundCoord(val)
    return math.floor(val * 5 + 0.5) / 5
end

local function makePosKey(x, y, z)
    return string.format("%.1f:%.1f:%.1f", roundCoord(x), roundCoord(y), roundCoord(z))
end

local function makeFullHash(modelId, x, y, z)
    return string.format("%d:0:%s", modelId, makePosKey(x, y, z))
end

local function getChunkKeyFromCoords(x, y)
    local cx = math.floor(x / CHUNK_SIZE)
    local cy = math.floor(y / CHUNK_SIZE)
    return cx * 10000 + cy
end

local function gridInsert(hash, obj)
    local key = getChunkKeyFromCoords(obj.x, obj.y)
    local cell = spatialGrid[key]
    if not cell then
        cell = {}
        spatialGrid[key] = cell
    end
    cell[hash] = obj
end

local function gridRemove(hash, obj)
    if not obj then return end
    local key = getChunkKeyFromCoords(obj.x, obj.y)
    local cell = spatialGrid[key]
    if cell then
        cell[hash] = nil
    end
end

local function getObjectModelSize(modelId, fallbackSize)
    if modelSizeCache[modelId] then return modelSizeCache[modelId] end
    if hasModelLoaded(modelId) then
        local ok, minX, minY, minZ, maxX, maxY, maxZ = pcall(getModelDimensions, modelId)
        if ok and minX and maxX then
            local dx = math.abs(maxX - minX)
            local dy = math.abs(maxY - minY)
            local dz = math.abs(maxZ - minZ)
            local diag = math.sqrt(dx * dx + dy * dy + dz * dz)
            local spanXY = math.max(dx, dy)
            local effective = diag
            if dz >= 5.5 then
                effective = math.max(effective, dz * 1.75)
            elseif dz >= 3.2 then
                effective = math.max(effective, dz * 1.35)
            end
            if spanXY >= 4.5 and dz >= 1.2 then
                effective = math.max(effective, spanXY * 1.45)
            end
            if effective > 0.05 and effective < 2500.0 then
                effective = math.floor(effective * 100 + 0.5) / 100
                modelSizeCache[modelId] = effective
                return effective
            end
        end
    end
    if fallbackSize and fallbackSize ~= 5.0 and fallbackSize ~= 6.0 and fallbackSize > 0.05 then
        return fallbackSize
    end
    return 6.0
end

local function getSizeTier(size)
    if size >= SIZE_LARGE then return 3
    elseif size <= SIZE_SMALL then return 1
    else return 2 end
end

local function getAllowedDistanceForSize(size)
    if not cfg.prioritizeLarge then return cfg.distLarge end
    if size >= SIZE_LARGE then
        return cfg.distLarge
    elseif size <= SIZE_SMALL then
        return cfg.distSmall
    else
        return cfg.distMedium
    end
end

local function isInvisibleMaterial(mId, lib, tex, col)
    local l = (lib or ""):lower()
    local t = (tex or ""):lower()
    if l == "none" or t == "none" or l == "null" or t == "null" then
        return true
    end
    if col and col ~= 0 and bit.band(bit.rshift(col, 24), 0xFF) == 0 then
        return true
    end
    return false
end

local function isPureBarrierModel(modelId)
    if not modelId then return false end
    if modelId == 18631 or modelId == 19300 then return true end
    if modelId >= 19353 and modelId <= 19486 then return true end
    return false
end

local function evaluateObjectInvisibility(obj)
    if not obj or not isPureBarrierModel(obj.m) then return false end
    if not obj.mat and not obj.mtxt then return false end
    local hasInvisible = false
    local hasVisible = false
    if obj.mat then
        for _, m in pairs(obj.mat) do
            if isInvisibleMaterial(m.m, m.l, m.t, m.c) then
                hasInvisible = true
            else
                hasVisible = true
            end
        end
    end
    if obj.mtxt then
        for _, mt in pairs(obj.mtxt) do
            local cleanTxt = (mt.t or ""):gsub("%s+", "")
            local backAlpha = mt.bc and bit.band(bit.rshift(mt.bc, 24), 0xFF) or 0
            if cleanTxt == "" and backAlpha == 0 then
                hasInvisible = true
            else
                hasVisible = true
            end
        end
    end
    return hasInvisible and not hasVisible
end

local function emulDestroySampId(sampId)
    isInternalEmul = true
    local bs = raknetNewBitStream()
    raknetBitStreamWriteInt16(bs, sampId)
    raknetEmulRpcReceiveBitStream(47, bs)
    raknetDeleteBitStream(bs)
    isInternalEmul = false
end

local function emulApplySingleMaterial(sampId, m)
    isInternalEmul = true
    local mbs = raknetNewBitStream()
    local l = m.l or "none"
    local t = m.t or "none"
    raknetBitStreamWriteInt16(mbs, sampId)
    raknetBitStreamWriteInt8(mbs, 1)
    raknetBitStreamWriteInt8(mbs, m.i or 0)
    raknetBitStreamWriteInt16(mbs, m.m or 0)
    raknetBitStreamWriteInt8(mbs, #l)
    raknetBitStreamWriteString(mbs, l)
    raknetBitStreamWriteInt8(mbs, #t)
    raknetBitStreamWriteString(mbs, t)
    raknetBitStreamWriteInt32(mbs, m.c or 0)
    raknetEmulRpcReceiveBitStream(84, mbs)
    raknetDeleteBitStream(mbs)
    isInternalEmul = false
end

local function emulApplySingleMaterialText(sampId, mt)
    isInternalEmul = true
    pcall(function()
        local tbs = raknetNewBitStream()
        local f = mt.f or "Arial"
        local txt = mt.t or ""
        raknetBitStreamWriteInt16(tbs, sampId)
        raknetBitStreamWriteInt8(tbs, 2)
        raknetBitStreamWriteInt8(tbs, mt.i or 0)
        raknetBitStreamWriteInt8(tbs, mt.s or 10)
        raknetBitStreamWriteInt8(tbs, #f)
        raknetBitStreamWriteString(tbs, f)
        raknetBitStreamWriteInt8(tbs, mt.fs or 24)
        raknetBitStreamWriteInt8(tbs, mt.b or 1)
        raknetBitStreamWriteInt32(tbs, mt.fc or -1)
        raknetBitStreamWriteInt32(tbs, mt.bc or 0)
        raknetBitStreamWriteInt8(tbs, mt.a or 0)
        raknetBitStreamEncodeString(tbs, txt)
        raknetEmulRpcReceiveBitStream(84, tbs)
        raknetDeleteBitStream(tbs)
    end)
    isInternalEmul = false
end

local function emulCreateSampObject(sampId, obj, maxDist)
    isInternalEmul = true
    local bs = raknetNewBitStream()
    raknetBitStreamWriteInt16(bs, sampId)
    raknetBitStreamWriteInt32(bs, obj.m)
    raknetBitStreamWriteFloat(bs, obj.x)
    raknetBitStreamWriteFloat(bs, obj.y)
    raknetBitStreamWriteFloat(bs, obj.z)
    raknetBitStreamWriteFloat(bs, obj.rx or 0.0)
    raknetBitStreamWriteFloat(bs, obj.ry or 0.0)
    raknetBitStreamWriteFloat(bs, obj.rz or 0.0)
    raknetBitStreamWriteFloat(bs, math.max(300.0, maxDist or cfg.distLarge))
    raknetBitStreamWriteInt8(bs, 0)
    raknetBitStreamWriteInt16(bs, 65535)
    raknetBitStreamWriteInt16(bs, 65535)
    raknetBitStreamWriteInt8(bs, 0)
    raknetEmulRpcReceiveBitStream(44, bs)
    raknetDeleteBitStream(bs)
    isInternalEmul = false

    if obj.mat then
        for _, m in pairs(obj.mat) do
            emulApplySingleMaterial(sampId, m)
        end
    end
    if obj.mtxt then
        for _, mt in pairs(obj.mtxt) do
            emulApplySingleMaterialText(sampId, mt)
        end
    end
end

local function findFreeSampSlot(avoidId)
    if usedSampCount >= MAX_SAMP_SLOTS then return nil end
    local id = nextSlotCursor
    for _ = 1, 800 do
        if id ~= avoidId and not serverStreamedById[id] and not localSampById[id] then
            local h = sampGetObjectHandleBySampId(id)
            if not h or h == 0 then
                nextSlotCursor = (id > 200) and (id - 1) or 999
                return id
            end
        end
        id = (id > 200) and (id - 1) or 999
    end
    return nil
end

local function getEntryHandle(entry)
    if not entry then return nil end
    if entry.sampId then
        local h = sampGetObjectHandleBySampId(entry.sampId)
        if h and h ~= 0 and doesObjectExist(h) then return h end
        return nil
    end
    if entry.handle and doesObjectExist(entry.handle) then
        return entry.handle
    end
    return nil
end

local function isLocalHandleValid(entry)
    return getEntryHandle(entry) ~= nil
end

local function updateLocalCollision(entry, enableCol)
    if not entry or entry.col == enableCol then return end
    local h = getEntryHandle(entry)
    if h then
        setObjectCollision(h, enableCol)
        entry.col = enableCol
    end
end

local function destroyLocalHandle(hash, skipRpc)
    local entry = spawnedLocal[hash]
    if not entry then return end
    if entry.sampId then
        local sId = entry.sampId
        localSampById[sId] = nil
        usedSampCount = math.max(0, usedSampCount - 1)
        nextSlotCursor = sId
        if not skipRpc then
            emulDestroySampId(sId)
        end
    elseif entry.handle and doesObjectExist(entry.handle) then
        deleteObject(entry.handle)
    end
    spawnedLocal[hash] = nil
    stats.renderedNow = math.max(0, stats.renderedNow - 1)
    stats.totalNow = stats.serverNow + stats.renderedNow
end

local function clearAllLocalObjects(restoreBlocked)
    spawnQueue = {}
    spawnQueueHead = 1
    deferredMatQueue = {}
    local toRestore = {}
    if restoreBlocked then
        for objId, hash in pairs(blockedServerIds) do
            if serverObjects[hash] then
                toRestore[objId] = serverObjects[hash]
            end
        end
    end
    blockedServerIds = {}
    for hash, _ in pairs(spawnedLocal) do
        destroyLocalHandle(hash)
    end
    spawnedLocal = {}
    localSampById = {}
    usedSampCount = 0
    nextSlotCursor = 999
    stats.renderedNow = 0
    for objId, obj in pairs(toRestore) do
        emulCreateSampObject(objId, obj, 300.0)
        stats.serverNow = stats.serverNow + 1
    end
    stats.totalNow = stats.serverNow
end

local function rebuildSpatialGrid()
    spatialGrid = {}
    local cnt = 0
    for hash, obj in pairs(serverObjects) do
        cnt = cnt + 1
        gridInsert(hash, obj)
    end
    stats.totalCached = cnt
end

local function getServerFilePath(serverKey)
    return serversFolder .. (serverKey or currentServerKey) .. '.json'
end

local function saveServerDatabase(force)
    if currentServerKey == "offline" then return end
    if not dbDirty and not force then return end
    save_json(getServerFilePath(currentServerKey), serverObjects)
    dbDirty = false
    lastSaveTime = os.clock()
end

local function ensureObjectModelsLoaded(obj)
    local mId = obj.m
    if not isModelAvailable(mId) then return false end
    local allReady = true
    if not hasModelLoaded(mId) then
        requestModel(mId)
        allReady = false
    end
    if obj.mat then
        for _, m in pairs(obj.mat) do
            local refM = m.m
            if refM and refM > 0 and refM ~= 65535 and isModelAvailable(refM) and not hasModelLoaded(refM) then
                requestModel(refM)
                allReady = false
            end
        end
    end
    return allReady
end

local function spawnSingleCachedObject(hash, obj, maxDist, colState, avoidSlotId)
    if spawnedLocal[hash] then return false, false end
    local sId = serverStreamedByHash[hash]
    if sId and not blockedServerIds[sId] then return false, false end
    if not ensureObjectModelsLoaded(obj) then return false, false end

    local mId = obj.m
    local hasMaterials = (obj.mat ~= nil or obj.mtxt ~= nil)

    if hasMaterials or usedSampCount < MAX_SAMP_SLOTS then
        local slot = findFreeSampSlot(avoidSlotId)
        if slot then
            emulCreateSampObject(slot, obj, maxDist)
            localSampById[slot] = hash
            usedSampCount = usedSampCount + 1
            local entry = { sampId = slot }
            spawnedLocal[hash] = entry
            updateLocalCollision(entry, colState)
            stats.renderedNow = stats.renderedNow + 1
            stats.totalNow = stats.serverNow + stats.renderedNow
            return true, hasMaterials
        end
        if hasMaterials then
            return false, false
        end
    end

    local ok, newObj = pcall(createObject, mId, obj.x, obj.y, obj.z)
    if ok and newObj and doesObjectExist(newObj) then
        setObjectCoordinates(newObj, obj.x, obj.y, obj.z)
        setObjectRotation(newObj, obj.rx or 0.0, obj.ry or 0.0, obj.rz or 0.0)
        setObjectCollision(newObj, colState)
        setObjectDynamic(newObj, false)
        spawnedLocal[hash] = { handle = newObj, col = colState }
        stats.renderedNow = stats.renderedNow + 1
        stats.totalNow = stats.serverNow + stats.renderedNow
        return true, false
    end
    return false, false
end

local function relocateLocalSampSlot(conflictId)
    local hash = localSampById[conflictId]
    if not hash then return end
    local entry = spawnedLocal[hash]
    local obj = serverObjects[hash]
    local oldCol = (entry and entry.col ~= false)
    destroyLocalHandle(hash, false)
    if obj and cfg.enabled and not inInteriorWorld then
        local maxDist = getAllowedDistanceForSize(obj.s or 6.0)
        spawnSingleCachedObject(hash, obj, maxDist, oldCol, conflictId)
    else
        forceStreamTick = true
    end
end

local function queueLocalMaterialUpdate(hash, obj, matEntry, isText)
    table.insert(deferredMatQueue, {
        hash = hash,
        obj = obj,
        entry = matEntry,
        isText = isText
    })
end

local function processDeferredMatQueue()
    if #deferredMatQueue == 0 then return end
    for i = 1, #deferredMatQueue do
        local item = deferredMatQueue[i]
        local localEntry = spawnedLocal[item.hash]
        if localEntry and isLocalHandleValid(localEntry) then
            if localEntry.sampId then
                if item.isText then
                    emulApplySingleMaterialText(localEntry.sampId, item.entry)
                else
                    emulApplySingleMaterial(localEntry.sampId, item.entry)
                end
            else
                local oldCol = (localEntry.col ~= false)
                destroyLocalHandle(item.hash)
                local maxDist = getAllowedDistanceForSize(item.obj.s or 6.0)
                spawnSingleCachedObject(item.hash, item.obj, maxDist, oldCol)
            end
        end
    end
    deferredMatQueue = {}
end

local function upsertServerObject(hash, modelId, x, y, z, rx, ry, rz, mats, matTexts, now)
    if dynamicBlacklist[makePosKey(x, y, z)] then return nil end
    local existing = serverObjects[hash]
    local computedSize = getObjectModelSize(modelId, existing and existing.s)
    if not existing then
        local newEntry = {
            m = modelId,
            x = math.floor(x * 100 + 0.5) / 100,
            y = math.floor(y * 100 + 0.5) / 100,
            z = math.floor(z * 100 + 0.5) / 100,
            rx = math.floor(rx * 100 + 0.5) / 100,
            ry = math.floor(ry * 100 + 0.5) / 100,
            rz = math.floor(rz * 100 + 0.5) / 100,
            s = computedSize,
            int = 0,
            mat = mats,
            mtxt = matTexts,
            seen = now
        }
        newEntry.inv = evaluateObjectInvisibility(newEntry) and 1 or nil
        serverObjects[hash] = newEntry
        gridInsert(hash, newEntry)
        stats.totalCached = stats.totalCached + 1
        dbDirty = true
        return newEntry
    else
        existing.s = computedSize
        existing.seen = now
        if mats then
            existing.mat = existing.mat or {}
            for k, v in pairs(mats) do existing.mat[k] = v end
            dbDirty = true
        end
        if matTexts then
            existing.mtxt = existing.mtxt or {}
            for k, v in pairs(matTexts) do existing.mtxt[k] = v end
            dbDirty = true
        end
        existing.inv = evaluateObjectInvisibility(existing) and 1 or nil
        return existing
    end
end

local function countNearbyCachedStreetObjects(px, py)
    local minCX = math.floor((px - 150.0) / CHUNK_SIZE)
    local maxCX = math.floor((px + 150.0) / CHUNK_SIZE)
    local minCY = math.floor((py - 150.0) / CHUNK_SIZE)
    local maxCY = math.floor((py + 150.0) / CHUNK_SIZE)
    local cnt = 0
    for cx = minCX, maxCX do
        local base = cx * 10000
        for cy = minCY, maxCY do
            local cell = spatialGrid[base + cy]
            if cell then
                for _, obj in pairs(cell) do
                    local dx, dy = obj.x - px, obj.y - py
                    if (dx * dx + dy * dy) <= 22500.0 then
                        cnt = cnt + 1
                        if cnt >= 15 then return cnt end
                    end
                end
            end
        end
    end
    return cnt
end

local function updateInteriorWorldState(px, py, pz)
    if getActiveInterior() ~= 0 or pz > 900.0 or pz < -50.0 then
        inInteriorWorld = true
        return
    end

    local srvTotal = 0
    local srvFar = 0
    local matchedInCache = 0

    for id, hash in pairs(serverStreamedById) do
        local obj = serverObjects[hash]
        if obj then
            matchedInCache = matchedInCache + 1
            srvTotal = srvTotal + 1
            local dx, dy, dz = obj.x - px, obj.y - py, obj.z - pz
            if (dx * dx + dy * dy + dz * dz) > 4900.0 then
                srvFar = srvFar + 1
            end
        else
            local h = sampGetObjectHandleBySampId(id)
            if h and h ~= 0 and doesObjectExist(h) then
                srvTotal = srvTotal + 1
                local ok, ox, oy, oz = getObjectCoordinates(h)
                if ok then
                    local dx, dy, dz = ox - px, oy - py, oz - pz
                    if (dx * dx + dy * dy + dz * dz) > 4900.0 then
                        srvFar = srvFar + 1
                    end
                end
            end
        end
    end

    if srvFar >= 2 or matchedInCache >= 2 then
        inInteriorWorld = false
        return
    end

    if srvTotal >= 12 and srvFar == 0 and matchedInCache == 0 then
        local cachedNearby = countNearbyCachedStreetObjects(px, py)
        if cachedNearby >= 10 then
            inInteriorWorld = true
            return
        end
    end

    inInteriorWorld = false
end

local function scanExistingServerObjects()
    if not isSampAvailable() then return end
    local now = os.clock()
    local srvCnt = 0
    for id = 0, 999 do
        if not localSampById[id] then
            local h = sampGetObjectHandleBySampId(id)
            if h and h ~= 0 and doesObjectExist(h) then
                local mId = getObjectModel(h)
                local ok, x, y, z = getObjectCoordinates(h)
                if ok and mId then
                    local realSize = getObjectModelSize(mId)
                    local hash = makeFullHash(mId, x, y, z)
                    serverStreamedById[id] = hash
                    serverStreamedByHash[hash] = id
                    blockedServerIds[id] = nil
                    srvCnt = srvCnt + 1
                    destroyLocalHandle(hash)
                    if serverObjects[hash] then
                        serverObjects[hash].seen = now
                        serverObjects[hash].s = realSize
                    end
                end
            end
        end
    end
    stats.serverNow = srvCnt
    stats.totalNow = stats.serverNow + stats.renderedNow
end

local function loadServerDatabase(serverKey)
    clearAllLocalObjects(false)
    serverObjects = {}
    spatialGrid = {}
    dynamicBlacklist = {}
    serverStreamedById = {}
    serverStreamedByHash = {}
    blockedServerIds = {}
    stats.autoRemoved = 0
    local path = getServerFilePath(serverKey)
    if file_exists(path) then
        local data = load_json(path)
        if type(data) == "table" then
            for _, obj in pairs(data) do
                if type(obj) == "table" and obj.m and obj.x and obj.y and obj.z and (obj.int == nil or obj.int == 0) then
                    local normHash = makeFullHash(obj.m, obj.x, obj.y, obj.z)
                    obj.s = getObjectModelSize(obj.m, obj.s)
                    obj.int = 0
                    obj.seen = os.clock()
                    obj.inv = evaluateObjectInvisibility(obj) and 1 or nil
                    serverObjects[normHash] = obj
                end
            end
        end
    end
    rebuildSpatialGrid()
    scanExistingServerObjects()
    dbDirty = false
end

local function ApplyStyle()
    local acc = imgui.ImVec4(0.18, 0.35, 0.58, 1.0)
    local bg = imgui.ImVec4(0.25, 0.25, 0.25, 1.0)
    imgui.PushStyleColor(imgui.Col.WindowBg, imgui.ImVec4(0.06, 0.06, 0.06, 0.98))
    imgui.PushStyleColor(imgui.Col.PopupBg, imgui.ImVec4(0.06, 0.06, 0.06, 0.98))
    imgui.PushStyleColor(imgui.Col.Border, imgui.ImVec4(0.22, 0.22, 0.22, 0.80))
    imgui.PushStyleColor(imgui.Col.Button, acc)
    imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(0.28, 0.45, 0.68, 1.0))
    imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(0.12, 0.25, 0.48, 1.0))
    imgui.PushStyleColor(imgui.Col.Header, acc)
    imgui.PushStyleColor(imgui.Col.HeaderHovered, imgui.ImVec4(0.28, 0.45, 0.68, 0.8))
    imgui.PushStyleColor(imgui.Col.HeaderActive, imgui.ImVec4(0.12, 0.25, 0.48, 1.0))
    imgui.PushStyleColor(imgui.Col.FrameBg, bg)
    imgui.PushStyleColor(imgui.Col.FrameBgHovered, imgui.ImVec4(0.35, 0.35, 0.35, 0.8))
    imgui.PushStyleColor(imgui.Col.FrameBgActive, bg)
    imgui.PushStyleColor(imgui.Col.SliderGrab, acc)
    imgui.PushStyleColor(imgui.Col.SliderGrabActive, imgui.ImVec4(0.28, 0.45, 0.68, 1.0))
    imgui.PushStyleColor(imgui.Col.CheckMark, acc)
    imgui.PushStyleColor(imgui.Col.TextSelectedBg, imgui.ImVec4(acc.x, acc.y, acc.z, 0.5))
end

function checkUpdates(is_manual)
    if not cfg.autoUpdate and not is_manual then return end
    local updateFile_tmp = cacheFolder .. 'chunky_update_' .. tostring(math.random(100000, 999999)) .. '.json'
    activeTempFiles[updateFile_tmp] = true
    if is_manual then showSystemNotification(u8"Проверка обновлений...", 3) end
    downloadUrlToFile(updateUrl .. "?t=" .. tostring(os.time()), updateFile_tmp, function(id, status)
        if status == dlstatus.STATUS_ENDDOWNLOADDATA then
            local f = io.open(updateFile_tmp, "rb")
            local content = nil
            if f then content = f:read("*a") f:close() end
            pcall(os.remove, updateFile_tmp)
            activeTempFiles[updateFile_tmp] = nil
            if content and content ~= "" then
                local data = nil
                local ok, res = pcall(decodeJson, content)
                if ok and type(res) == "table" then
                    data = res
                else
                    pcall(function()
                        local func = load("return " .. content)
                        if func then data = func() end
                    end)
                end
                if data and data.version and data.url then
                    if tonumber(data.version) > tonumber(script_version) then
                        local is_silent = (data.silent == true) and not is_manual
                        if not is_silent then showSystemNotification(u8"Найдено обновление! Загрузка...", 3) end
                        lua_thread.create(function()
                            wait(100)
                            local scriptPath = thisScript().path
                            local tempPath = scriptPath .. tostring(math.random(10000, 99999)) .. ".tmp"
                            activeTempFiles[tempPath] = true
                            downloadUrlToFile(data.url .. "?t=" .. tostring(os.time()), tempPath, function(id2, status2)
                                if status2 == dlstatus.STATUS_ENDDOWNLOADDATA then
                                    local fTmp = io.open(tempPath, "rb")
                                    if fTmp then
                                        local newCode = fTmp:read("*a")
                                        fTmp:close()
                                        pcall(os.remove, tempPath)
                                        activeTempFiles[tempPath] = nil
                                        if newCode:find("\208[\128-\191]") or newCode:find("\209[\128-\191]") then
                                            local decoded = u8:decode(newCode)
                                            if decoded then newCode = decoded end
                                        end
                                        local fOut = io.open(scriptPath, "wb")
                                        if fOut then
                                            fOut:write(newCode)
                                            fOut:close()
                                            saveServerDatabase(true)
                                            if not is_silent then showSystemNotification(u8"Успешно обновлено! Перезапуск...", 1) end
                                            lua_thread.create(function() wait(1500) thisScript():reload() end)
                                        elseif not is_silent then
                                            showSystemNotification(u8"Ошибка: Файл скрипта занят!", 2)
                                        end
                                    end
                                elseif status2 == dlstatus.STATUS_EX_ERROR then
                                    pcall(os.remove, tempPath)
                                    activeTempFiles[tempPath] = nil
                                    if not is_silent then showSystemNotification(u8"Ошибка при скачивании обновления!", 2) end
                                end
                            end)
                        end)
                    elseif is_manual then
                        showSystemNotification(u8"У вас установлена последняя версия!", 1)
                    end
                elseif is_manual then
                    showSystemNotification(u8"Ошибка: Неверный формат ответа!", 2)
                end
            elseif is_manual then
                showSystemNotification(u8"Ошибка: Пустой ответ от GitHub!", 2)
            end
        elseif status == dlstatus.STATUS_EX_ERROR then
            pcall(os.remove, updateFile_tmp)
            activeTempFiles[updateFile_tmp] = nil
            if is_manual then showSystemNotification(u8"Ошибка соединения с GitHub!", 2) end
        end
    end)
end

function samp.onSetPlayerPos(pos)
    lastTeleportTime = os.clock()
    if pos and (pos.z > 900.0 or pos.z < -50.0) then
        inInteriorWorld = true
        clearAllLocalObjects(true)
    end
end

function samp.onSetInterior(intId)
    lastTeleportTime = os.clock()
    if intId ~= 0 then
        inInteriorWorld = true
        clearAllLocalObjects(true)
    end
end

function samp.onCreateObject(objectId, data)
    if isInternalEmul then return end

    local prevHash = serverStreamedById[objectId]
    if prevHash then
        if serverStreamedByHash[prevHash] == objectId then
            serverStreamedByHash[prevHash] = nil
        end
        serverStreamedById[objectId] = nil
        blockedServerIds[objectId] = nil
    end

    if not data or not data.position or not data.rotation then
        if localSampById[objectId] then relocateLocalSampSlot(objectId) end
        return
    end
    if (data.attachToVehicleId and data.attachToVehicleId ~= 65535) or (data.attachToObjectId and data.attachToObjectId ~= 65535) then
        if localSampById[objectId] then relocateLocalSampSlot(objectId) end
        return
    end

    local now = os.clock()
    lastServerCreateTime = now

    local x, y, z = data.position.x, data.position.y, data.position.z
    local rx, ry, rz = data.rotation.x, data.rotation.y, data.rotation.z
    local hash = makeFullHash(data.modelId, x, y, z)

    local parsedMats = nil
    if type(data.materials) == "table" and #data.materials > 0 then
        parsedMats = {}
        for _, m in ipairs(data.materials) do
            local idx = m.materialId or 0
            parsedMats[idx] = {
                i = idx,
                m = m.modelId or 0,
                l = m.libraryName or "none",
                t = m.textureName or "none",
                c = m.color or 0
            }
        end
    end

    local parsedMtxt = nil
    local matTextList = data.materials_text or data.materialText
    if type(matTextList) == "table" and #matTextList > 0 then
        parsedMtxt = {}
        for _, mt in ipairs(matTextList) do
            local idx = mt.materialId or 0
            parsedMtxt[idx] = {
                i = idx,
                s = mt.materialSize or 10,
                f = mt.fontName or "Arial",
                fs = mt.fontSize or 24,
                b = mt.bold and 1 or 0,
                fc = mt.fontColor or -1,
                bc = mt.backColor or 0,
                a = mt.align or 0,
                t = mt.text or ""
            }
        end
    end

    serverStreamedById[objectId] = hash
    serverStreamedByHash[hash] = objectId

    local isOutdoor = (getActiveInterior() == 0 and z <= 900.0 and z >= -50.0 and not inInteriorWorld)
    local cachedObj = serverObjects[hash]

    if isOutdoor and cfg.recordMapping then
        cachedObj = upsertServerObject(hash, data.modelId, x, y, z, rx, ry, rz, parsedMats, parsedMtxt, now)
    elseif cachedObj then
        cachedObj.seen = now
    end

    local localEntry = spawnedLocal[hash]
    if cfg.enabled and isOutdoor and cachedObj and localEntry and isLocalHandleValid(localEntry) then
        if localSampById[objectId] and localSampById[objectId] ~= hash then
            relocateLocalSampSlot(objectId)
        end
        updateLocalCollision(localEntry, true)
        blockedServerIds[objectId] = hash

        if parsedMats then
            for _, matEntry in pairs(parsedMats) do
                queueLocalMaterialUpdate(hash, cachedObj, matEntry, false)
            end
        end
        if parsedMtxt then
            for _, txtEntry in pairs(parsedMtxt) do
                queueLocalMaterialUpdate(hash, cachedObj, txtEntry, true)
            end
        end

        return false
    end

    if localSampById[objectId] then
        relocateLocalSampSlot(objectId)
    end

    destroyLocalHandle(hash)
    stats.serverNow = stats.serverNow + 1
    stats.totalNow = stats.serverNow + stats.renderedNow
end

function samp.onSetObjectMaterial(a, b)
    if isInternalEmul then return end
    local objectId = type(a) == "number" and a or (type(a) == "table" and a.objectId)
    local m = type(b) == "table" and b or (type(a) == "table" and a)
    if not objectId or not m then return end

    local idx = m.materialId or 0
    local mId = m.modelId or 0
    local lib = m.libraryName or "none"
    local tex = m.textureName or "none"
    local col = m.color or 0
    local matEntry = { i = idx, m = mId, l = lib, t = tex, c = col }

    local hash = serverStreamedById[objectId]
    if hash and serverObjects[hash] and not inInteriorWorld then
        local obj = serverObjects[hash]
        obj.mat = obj.mat or {}
        local cur = obj.mat[idx]
        local isChanged = (not cur or cur.m ~= mId or cur.l ~= lib or cur.t ~= tex or cur.c ~= col)
        if isChanged then
            obj.mat[idx] = matEntry
            obj.inv = evaluateObjectInvisibility(obj) and 1 or nil
            dbDirty = true
            if obj.inv == 1 then
                destroyLocalHandle(hash)
            elseif blockedServerIds[objectId] then
                queueLocalMaterialUpdate(hash, obj, matEntry, false)
            end
        end
    end

    if blockedServerIds[objectId] then
        return false
    end
end

function samp.onSetObjectMaterialText(a, b)
    if isInternalEmul then return end
    local objectId = type(a) == "number" and a or (type(a) == "table" and a.objectId)
    local mt = type(b) == "table" and b or (type(a) == "table" and a)
    if not objectId or not mt then return end

    local idx = mt.materialId or 0
    local txt = mt.text or ""
    local txtEntry = {
        i = idx,
        s = mt.materialSize or 10,
        f = mt.fontName or "Arial",
        fs = mt.fontSize or 24,
        b = mt.bold and 1 or 0,
        fc = mt.fontColor or -1,
        bc = mt.backColor or 0,
        a = mt.align or 0,
        t = txt
    }

    local hash = serverStreamedById[objectId]
    if hash and serverObjects[hash] and not inInteriorWorld then
        local obj = serverObjects[hash]
        obj.mtxt = obj.mtxt or {}
        local cur = obj.mtxt[idx]
        local isChanged = (not cur or cur.t ~= txt or cur.fc ~= txtEntry.fc or cur.bc ~= txtEntry.bc)
        if isChanged then
            obj.mtxt[idx] = txtEntry
            obj.inv = evaluateObjectInvisibility(obj) and 1 or nil
            dbDirty = true
            if obj.inv == 1 then
                destroyLocalHandle(hash)
            elseif blockedServerIds[objectId] then
                queueLocalMaterialUpdate(hash, obj, txtEntry, true)
            end
        end
    end

    if blockedServerIds[objectId] then
        return false
    end
end

function samp.onSetObjectRotation(objectId, rot)
    if isInternalEmul or not rot then return end
    local rx = math.floor(rot.x * 100 + 0.5) / 100
    local ry = math.floor(rot.y * 100 + 0.5) / 100
    local rz = math.floor(rot.z * 100 + 0.5) / 100

    local hash = serverStreamedById[objectId]
    if hash and serverObjects[hash] and not inInteriorWorld then
        serverObjects[hash].rx = rx
        serverObjects[hash].ry = ry
        serverObjects[hash].rz = rz
        dbDirty = true
        if blockedServerIds[objectId] then
            local entry = spawnedLocal[hash]
            if entry then
                local h = getEntryHandle(entry)
                if h then setObjectRotation(h, rx, ry, rz) end
            end
            return false
        end
    end
end

function samp.onSetObjectPos(objectId, pos)
    if isInternalEmul or not pos then return end
    local hash = serverStreamedById[objectId]
    if hash and serverObjects[hash] and not inInteriorWorld then
        local obj = serverObjects[hash]
        local nx = math.floor(pos.x * 100 + 0.5) / 100
        local ny = math.floor(pos.y * 100 + 0.5) / 100
        local nz = math.floor(pos.z * 100 + 0.5) / 100
        local newHash = makeFullHash(obj.m, nx, ny, nz)
        gridRemove(hash, obj)
        serverObjects[hash] = nil
        obj.x, obj.y, obj.z = nx, ny, nz
        serverObjects[newHash] = obj
        gridInsert(newHash, obj)
        serverStreamedById[objectId] = newHash
        serverStreamedByHash[hash] = nil
        serverStreamedByHash[newHash] = objectId
        dbDirty = true

        if spawnedLocal[hash] then
            local entry = spawnedLocal[hash]
            spawnedLocal[hash] = nil
            spawnedLocal[newHash] = entry
            if entry.sampId then localSampById[entry.sampId] = newHash end
            local h = getEntryHandle(entry)
            if h then setObjectCoordinates(h, nx, ny, nz) end
        end
        if blockedServerIds[objectId] then
            blockedServerIds[objectId] = newHash
            return false
        end
    end
end

function samp.onDestroyObject(objectId)
    if isInternalEmul then return end

    local wasBlocked = blockedServerIds[objectId]
    blockedServerIds[objectId] = nil

    local hash = serverStreamedById[objectId]
    if hash then
        if serverStreamedByHash[hash] == objectId then
            serverStreamedByHash[hash] = nil
        end
        serverStreamedById[objectId] = nil
        if not wasBlocked then
            stats.serverNow = math.max(0, stats.serverNow - 1)
            stats.totalNow = stats.serverNow + stats.renderedNow
        end

        if serverObjects[hash] then
            serverObjects[hash].seen = os.clock()
            serverObjects[hash].s = getObjectModelSize(serverObjects[hash].m, serverObjects[hash].s)
            if not wasBlocked then
                forceStreamTick = true
            end
        end
    end

    if wasBlocked then
        return false
    end
end

function samp.onMoveObject(objectId)
    if isInternalEmul then return end
    local wasBlocked = blockedServerIds[objectId]
    blockedServerIds[objectId] = nil

    local hash = serverStreamedById[objectId]
    if hash then
        destroyLocalHandle(hash)
        local obj = serverObjects[hash]
        if obj then
            dynamicBlacklist[makePosKey(obj.x, obj.y, obj.z)] = true
            gridRemove(hash, obj)
            serverObjects[hash] = nil
            stats.totalCached = math.max(0, stats.totalCached - 1)
            dbDirty = true
            if wasBlocked then
                if localSampById[objectId] then relocateLocalSampSlot(objectId) end
                emulCreateSampObject(objectId, obj, 300.0)
            end
        end
    end
end

local function verifyServerStreamTable(now)
    local unblockedSrvCnt = 0
    for id, hash in pairs(serverStreamedById) do
        local obj = serverObjects[hash]
        if blockedServerIds[id] then
            if obj then
                local mId = obj.m
                if not modelSizeCache[mId] and hasModelLoaded(mId) then
                    obj.s = getObjectModelSize(mId)
                    dbDirty = true
                end
                obj.seen = now
                local entry = spawnedLocal[hash]
                if not entry or not isLocalHandleValid(entry) then
                    if entry then destroyLocalHandle(hash, true) end
                    local maxDist = getAllowedDistanceForSize(obj.s or 6.0)
                    spawnSingleCachedObject(hash, obj, maxDist, true)
                end
            else
                blockedServerIds[id] = nil
                serverStreamedById[id] = nil
                if serverStreamedByHash[hash] == id then
                    serverStreamedByHash[hash] = nil
                end
            end
        else
            local h = sampGetObjectHandleBySampId(id)
            if not h or h == 0 then
                serverStreamedById[id] = nil
                if serverStreamedByHash[hash] == id then
                    serverStreamedByHash[hash] = nil
                end
            else
                unblockedSrvCnt = unblockedSrvCnt + 1
                if obj then
                    local mId = obj.m
                    if not modelSizeCache[mId] and hasModelLoaded(mId) then
                        obj.s = getObjectModelSize(mId)
                        dbDirty = true
                    end
                    obj.seen = now
                end
            end
        end
    end
    stats.serverNow = unblockedSrvCnt
end

local function processSpawnQueue(now)
    if inInteriorWorld or spawnQueueHead > #spawnQueue then return end
    if now - lastServerCreateTime < 0.20 then return end

    local maxSpawnsNow = math.floor(spawnBudget)
    if maxSpawnsNow <= 0 then return end

    local spawnedTotal = 0
    local spawnedTextured = 0
    local requestedModels = 0
    local frameMaxTotal = math.min(maxSpawnsNow, 10)
    local frameMaxTextured = 2

    while spawnQueueHead <= #spawnQueue and spawnedTotal < frameMaxTotal and requestedModels < 4 do
        local item = spawnQueue[spawnQueueHead]
        local hash = item.hash
        local obj = item.obj
        spawnQueueHead = spawnQueueHead + 1

        local sId = serverStreamedByHash[hash]
        if obj and not spawnedLocal[hash] and (not sId or blockedServerIds[sId]) then
            if not ensureObjectModelsLoaded(obj) then
                requestedModels = requestedModels + 1
            else
                local hasMats = (obj.mat ~= nil or obj.mtxt ~= nil)
                if hasMats and spawnedTextured >= frameMaxTextured then
                    spawnQueueHead = spawnQueueHead - 1
                    break
                end
                local ok, wasMat = spawnSingleCachedObject(hash, obj, item.maxDist, item.col)
                if ok then
                    spawnedTotal = spawnedTotal + 1
                    if wasMat then spawnedTextured = spawnedTextured + 1 end
                end
            end
        end
    end

    spawnBudget = math.max(0.0, spawnBudget - spawnedTotal)
end

local function processStreamingTick()
    if not cfg.enabled or not sampIsLocalPlayerSpawned() or currentServerKey == "offline" then
        if next(spawnedLocal) ~= nil then clearAllLocalObjects(true) end
        return
    end

    if isPauseMenuActive() then return end

    local now = os.clock()
    local px, py, pz = getCharCoordinates(PLAYER_PED)
    verifyServerStreamTable(now)
    updateInteriorWorldState(px, py, pz)

    if inInteriorWorld then
        if next(spawnedLocal) ~= nil then
            clearAllLocalObjects(true)
        end
        return
    end

    local cx, cy, cz = getActiveCameraCoordinates()
    local tx, ty, tz = getActiveCameraPointAt()
    local fvx, fvy, fvz = tx - cx, ty - cy, tz - cz
    local fvLen = math.sqrt(fvx * fvx + fvy * fvy + fvz * fvz)
    if fvLen > 0.001 then
        fvx, fvy, fvz = fvx / fvLen, fvy / fvLen, fvz / fvLen
    else
        fvx, fvy, fvz = 0.0, 1.0, 0.0
    end

    local serverActive = next(serverStreamedById) ~= nil
    local canVerify = cfg.autoDeleteMissing and serverActive and (now - lastSpawnedClock > 5.0) and (now - lastTeleportTime > 4.0)

    local maxSearchDist = math.max(cfg.distLarge, cfg.distMedium, cfg.distSmall) + HYSTERESIS_MARGIN
    local minChunkX = math.floor((px - maxSearchDist) / CHUNK_SIZE)
    local maxChunkX = math.floor((px + maxSearchDist) / CHUNK_SIZE)
    local minChunkY = math.floor((py - maxSearchDist) / CHUNK_SIZE)
    local maxChunkY = math.floor((py + maxSearchDist) / CHUNK_SIZE)

    local candidates = {}
    local toRemove = {}

    for chX = minChunkX, maxChunkX do
        local baseKey = chX * 10000
        for chY = minChunkY, maxChunkY do
            local cell = spatialGrid[baseKey + chY]
            if cell then
                for hash, obj in pairs(cell) do
                    if obj.inv == 1 then
                        if spawnedLocal[hash] then destroyLocalHandle(hash) end
                    else
                        local sId = serverStreamedByHash[hash]
                        local isBlockedServer = (sId ~= nil and blockedServerIds[sId] ~= nil)

                        if sId and not isBlockedServer then
                            if spawnedLocal[hash] then destroyLocalHandle(hash) end
                            obj.seen = now
                            obj.nearSince = nil
                        else
                            local dx, dy, dz = obj.x - px, obj.y - py, obj.z - pz
                            local distSq = dx * dx + dy * dy + dz * dz

                            if isBlockedServer then
                                obj.seen = now
                                obj.nearSince = nil
                            elseif canVerify then
                                if distSq <= VERIFY_RADIUS_SQ then
                                    if not obj.nearSince then
                                        obj.nearSince = now
                                    elseif now - obj.nearSince >= 3.5 and (not obj.seen or now - obj.seen >= 4.0) then
                                        table.insert(toRemove, hash)
                                    end
                                else
                                    obj.nearSince = nil
                                end
                            else
                                obj.nearSince = nil
                            end

                            local objSize = getObjectModelSize(obj.m, obj.s)
                            if modelSizeCache[obj.m] and obj.s ~= modelSizeCache[obj.m] then
                                obj.s = modelSizeCache[obj.m]
                                dbDirty = true
                            end

                            local tier = getSizeTier(objSize)
                            local maxDist = getAllowedDistanceForSize(objSize)
                            local isAlreadySpawned = (spawnedLocal[hash] ~= nil)
                            local activeMaxDist = isAlreadySpawned and (maxDist + HYSTERESIS_MARGIN) or maxDist
                            local activeMaxDistSq = activeMaxDist * activeMaxDist

                            if isBlockedServer or distSq <= activeMaxDistSq then
                                local keep360 = (tier >= 2) or isBlockedServer or isAlreadySpawned or (distSq < 4900.0)
                                local inFront = keep360
                                if not inFront then
                                    local cdx, cdy, cdz = obj.x - cx, obj.y - cy, obj.z - cz
                                    inFront = ((cdx * fvx + cdy * fvy + cdz * fvz) > -0.15)
                                end
                                local effDistSq = inFront and distSq or (distSq * 2.0)
                                if isAlreadySpawned then
                                    effDistSq = effDistSq * 0.85
                                end
                                table.insert(candidates, {
                                    hash = hash,
                                    obj = obj,
                                    distSq = distSq,
                                    effDistSq = effDistSq,
                                    inFront = inFront,
                                    pinned = isBlockedServer,
                                    spawned = isAlreadySpawned,
                                    maxDist = activeMaxDist,
                                    size = objSize,
                                    tier = tier
                                })
                            elseif isAlreadySpawned then
                                destroyLocalHandle(hash)
                            end
                        end
                    end
                end
            end
        end
    end

    if #toRemove > 0 then
        for _, hash in ipairs(toRemove) do
            destroyLocalHandle(hash)
            local obj = serverObjects[hash]
            if obj then
                gridRemove(hash, obj)
                serverObjects[hash] = nil
                stats.totalCached = math.max(0, stats.totalCached - 1)
                stats.autoRemoved = stats.autoRemoved + 1
                dbDirty = true
            end
        end
    end

    local totalLimit = math.max(1, cfg.maxLocalObjects)
    local allowedLocalSlots = math.max(0, totalLimit - stats.serverNow)
    local isOverLimit = (#candidates > allowedLocalSlots)

    table.sort(candidates, function(a, b)
        if a.pinned ~= b.pinned then
            return a.pinned
        end
        if cfg.prioritizeLarge then
            if a.tier ~= b.tier then
                return a.tier > b.tier
            end
            if isOverLimit and a.tier == 1 and a.inFront ~= b.inFront then
                return a.inFront
            end
            if isOverLimit and math.abs(a.size - b.size) > 1.5 then
                return a.size > b.size
            end
        end
        return a.effDistSq < b.effDistSq
    end)

    local desiredSet = {}
    local limit = math.min(#candidates, allowedLocalSlots)
    for i = 1, limit do
        desiredSet[candidates[i].hash] = true
    end

    for _, bHash in pairs(blockedServerIds) do
        desiredSet[bHash] = true
    end

    for hash, entry in pairs(spawnedLocal) do
        if not desiredSet[hash] or not isLocalHandleValid(entry) then
            destroyLocalHandle(hash)
        end
    end

    spawnQueue = {}
    spawnQueueHead = 1
    local activeCount = 0

    for i = 1, limit do
        local item = candidates[i]
        local hash = item.hash
        local entry = spawnedLocal[hash]
        local colState = item.pinned or (not cfg.disableFarCollision) or (item.distSq < COL_RADIUS_SQ)
        if entry then
            activeCount = activeCount + 1
            updateLocalCollision(entry, colState)
        else
            table.insert(spawnQueue, {
                hash = hash,
                obj = item.obj,
                maxDist = item.maxDist,
                col = colState
            })
        end
    end

    stats.renderedNow = activeCount
    stats.totalNow = stats.serverNow + stats.renderedNow
end

addEventHandler('onWindowMessage', function(msg, wparam, lparam)
    if (msg == 0x0100 or msg == 0x0101) and wparam == vkeys.VK_ESCAPE and UI.windowState[0] then
        consumeWindowMessage(true, false)
        if msg == 0x0100 then
            Sys.wasTypingEscape = imgui.GetIO().WantCaptureKeyboard
        elseif msg == 0x0101 then
            if not Sys.wasTypingEscape then
                UI.windowState[0] = false
            end
            Sys.wasTypingEscape = false
        end
    end
end)

function onScriptTerminate(scr, quitGame)
    if scr == thisScript() then
        if not quitGame then
            clearAllLocalObjects(true)
        end
        saveServerDatabase(false)
        for path, _ in pairs(activeTempFiles) do
            pcall(os.remove, path)
        end
    end
end

local notifFrame = imgui.OnFrame(
    function()
        return Sys.tempSysNotifText ~= nil and os.clock() < Sys.tempSysNotifTimer
    end,
    function()
        local resX, resY = getScreenResolution()
        local posX, posY = resX - 20, resY - 20
        local pivotX, pivotY = 1.0, 1.0

        if cfg.notifPos == 1 then
            posX, posY = 20, resY - 20
            pivotX, pivotY = 0.0, 1.0
        elseif cfg.notifPos == 2 then
            posX, posY = resX / 2, resY - 20
            pivotX, pivotY = 0.5, 1.0
        elseif cfg.notifPos == 3 then
            posX, posY = resX - 20, resY - 20
            pivotX, pivotY = 1.0, 1.0
        elseif cfg.notifPos == 4 then
            posX, posY = resX / 2, resY * 0.08
            pivotX, pivotY = 0.5, 0.0
        end

        local borderColor = imgui.ImVec4(0.25, 0.25, 0.25, 1.0)
        if Sys.tempSysNotifType == 1 then borderColor = imgui.ImVec4(0.20, 0.80, 0.20, 0.80)
        elseif Sys.tempSysNotifType == 2 then borderColor = imgui.ImVec4(0.80, 0.20, 0.20, 0.80)
        elseif Sys.tempSysNotifType == 3 then borderColor = imgui.ImVec4(0.20, 0.60, 0.90, 0.80) end

        imgui.SetNextWindowPos(imgui.ImVec2(posX, posY), imgui.Cond.Always, imgui.ImVec2(pivotX, pivotY))
        imgui.PushStyleColor(imgui.Col.WindowBg, imgui.ImVec4(0.08, 0.08, 0.08, 0.96))
        imgui.PushStyleColor(imgui.Col.Border, borderColor)
        imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.95, 0.95, 0.95, 1.0))
        imgui.PushStyleVarFloat(imgui.StyleVar.WindowRounding, 6.0)
        imgui.PushStyleVarFloat(imgui.StyleVar.WindowBorderSize, 1.0)
        imgui.PushStyleVarVec2(imgui.StyleVar.WindowPadding, imgui.ImVec2(15, 10))

        local flags = imgui.WindowFlags.NoTitleBar + imgui.WindowFlags.NoResize + imgui.WindowFlags.NoMove + imgui.WindowFlags.NoScrollbar + imgui.WindowFlags.AlwaysAutoResize + imgui.WindowFlags.NoFocusOnAppearing + imgui.WindowFlags.NoInputs
        if imgui.Begin("##ChunkySysIndicator", nil, flags) then
            imgui.Text(Sys.tempSysNotifText)
            imgui.End()
        end
        imgui.PopStyleVar(3)
        imgui.PopStyleColor(3)
    end
)
notifFrame.HideCursor = true

local mainFrame = imgui.OnFrame(
    function() return UI.windowState[0] end,
    function()
        local resX, resY = getScreenResolution()
        ApplyStyle()

        imgui.PushStyleVarFloat(imgui.StyleVar.FrameRounding, 6.0)
        imgui.PushStyleVarFloat(imgui.StyleVar.PopupRounding, 8.0)
        imgui.PushStyleVarFloat(imgui.StyleVar.WindowRounding, 10.0)
        imgui.PushStyleVarFloat(imgui.StyleVar.WindowBorderSize, 1.0)
        imgui.PushStyleVarVec2(imgui.StyleVar.WindowPadding, imgui.ImVec2(16, 14))

        imgui.SetNextWindowPos(imgui.ImVec2(resX / 2, resY / 2), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))

        local flags = imgui.WindowFlags.AlwaysAutoResize + imgui.WindowFlags.NoTitleBar + imgui.WindowFlags.NoScrollbar
        if imgui.Begin("##ChunkySettingsModal", UI.windowState, flags) then
            imgui.Text(u8"Настройки ChunkySA")
            imgui.SameLine()
            imgui.TextColored(imgui.ImVec4(0.5, 0.5, 0.5, 1.0), string.format("v%.2f", script_version))
            imgui.Spacing()

            local fieldWidth = 263
            local tripleWidth = 130
            local worldStatus = inInteriorWorld and " [Интерьер]" or ""
            imgui.Text(u8(string.format("База сервера (Объектов: %d/%d | Локальных: %d | В кэше: %d)%s:", stats.totalNow, cfg.maxLocalObjects, stats.renderedNow, stats.totalCached, worldStatus)))
            imgui.PushItemWidth(fieldWidth)
            if imgui.BeginCombo("##ServerDisplayCombo", u8(currentServerDisplay)) then
                imgui.Selectable(u8(currentServerDisplay), true)
                imgui.EndCombo()
            end
            imgui.PopItemWidth()

            imgui.SameLine()
            local isConfirming = (os.clock() < UI.confirmClearTimer)
            if isConfirming then
                imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(0.80, 0.20, 0.20, 1.0))
                imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(0.90, 0.30, 0.30, 1.0))
            end
            if imgui.Button(isConfirming and u8"Точно очистить?" or u8"Очистить базу", imgui.ImVec2(135, 0)) then
                if not isConfirming then
                    UI.confirmClearTimer = os.clock() + 3.0
                else
                    UI.confirmClearTimer = 0
                    clearAllLocalObjects(true)
                    serverObjects = {}
                    spatialGrid = {}
                    stats.totalCached = 0
                    stats.autoRemoved = 0
                    saveServerDatabase(true)
                    scanExistingServerObjects()
                    showSystemNotification(u8"База маппинга текущего сервера очищена!", 1)
                end
            end
            if isConfirming then imgui.PopStyleColor(2) end

            imgui.Spacing()
            imgui.Separator()
            imgui.Spacing()

            imgui.Text(u8"Пресеты настроек отображения:")
            for i, p in ipairs(presets) do
                if i > 1 then imgui.SameLine() end
                local isActivePreset = (cfg.maxLocalObjects == p.maxObj and cfg.spawnSpeed == p.speed and cfg.distLarge == p.dL and cfg.distMedium == p.dM and cfg.distSmall == p.dS)
                if isActivePreset then
                    imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(0.26, 0.50, 0.82, 1.0))
                end
                if imgui.Button(p.name, imgui.ImVec2(tripleWidth, 0)) then
                    cfg.maxLocalObjects = p.maxObj
                    cfg.spawnSpeed = p.speed
                    cfg.distLarge = p.dL
                    cfg.distMedium = p.dM
                    cfg.distSmall = p.dS
                    UI.maxObjBuf[0] = p.maxObj
                    saveSettings()
                    forceStreamTick = true
                    showSystemNotification(u8"Применен пресет: " .. p.name, 1)
                end
                if isActivePreset then
                    imgui.PopStyleColor(1)
                end
            end

            imgui.Spacing()
            imgui.Text(u8"Полный лимит объектов в зоне стрима:")
            UI.maxObjBuf[0] = cfg.maxLocalObjects
            imgui.PushItemWidth(fieldWidth)
            if imgui.InputInt("##MaxLocalObjects", UI.maxObjBuf, 50, 250) then
                cfg.maxLocalObjects = math.max(50, UI.maxObjBuf[0])
                saveSettings()
                forceStreamTick = true
            end
            imgui.PopItemWidth()

            imgui.Spacing()
            imgui.Text(u8"Скорость прогрузки объектов в секунду:")
            local iSpeed = imgui.new.int[1](cfg.spawnSpeed or 300)
            imgui.PushItemWidth(fieldWidth)
            if imgui.SliderInt("##SpawnSpeed", iSpeed, 25, 1000, u8"%d шт/сек") then
                cfg.spawnSpeed = iSpeed[0]
                saveSettings()
            end
            imgui.PopItemWidth()

            imgui.Spacing()
            imgui.Text(u8"Дальность прорисовки (Крупные / Средние / Мелкие):")
            imgui.PushItemWidth(tripleWidth)
            local fDistL = imgui.new.float[1](cfg.distLarge)
            if imgui.SliderFloat("##DistL", fDistL, 200.0, 1500.0, u8"%.0f м") then
                cfg.distLarge = fDistL[0]
                saveSettings()
            end
            imgui.SameLine()
            local fDistM = imgui.new.float[1](cfg.distMedium)
            if imgui.SliderFloat("##DistM", fDistM, 150.0, 1000.0, u8"%.0f м") then
                cfg.distMedium = fDistM[0]
                saveSettings()
            end
            imgui.SameLine()
            local fDistS = imgui.new.float[1](cfg.distSmall)
            if imgui.SliderFloat("##DistS", fDistS, 100.0, 600.0, u8"%.0f м") then
                cfg.distSmall = fDistS[0]
                saveSettings()
            end
            imgui.PopItemWidth()

            imgui.Spacing()
            imgui.Text(u8"Положение системных уведомлений:")
            imgui.PushItemWidth(fieldWidth)
            if imgui.BeginCombo("##NotifPosCombo", notifPositions[cfg.notifPos] or notifPositions[3]) then
                for i, posName in ipairs(notifPositions) do
                    if imgui.Selectable(posName, cfg.notifPos == i) then
                        cfg.notifPos = i
                        saveSettings()
                    end
                end
                imgui.EndCombo()
            end
            imgui.PopItemWidth()

            imgui.Spacing()
            imgui.Separator()
            imgui.Spacing()

            imgui.Text(u8"Дополнительные функции:")
            imgui.Spacing()

            local bEnabled = imgui.new.bool(cfg.enabled)
            if imgui.Checkbox(u8"Включить локальную прогрузку маппинга (ChunkySA)", bEnabled) then
                cfg.enabled = bEnabled[0]
                if not cfg.enabled then clearAllLocalObjects(true) else forceStreamTick = true end
                saveSettings()
            end

            local bRecord = imgui.new.bool(cfg.recordMapping)
            if imgui.Checkbox(u8"Автоматически сохранять новый маппинг сервера", bRecord) then
                cfg.recordMapping = bRecord[0]
                saveSettings()
            end

            local bAutoDel = imgui.new.bool(cfg.autoDeleteMissing)
            if imgui.Checkbox(u8"Автоудаление пропавших объектов со старых координат", bAutoDel) then
                cfg.autoDeleteMissing = bAutoDel[0]
                saveSettings()
            end

            local bPrio = imgui.new.bool(cfg.prioritizeLarge)
            if imgui.Checkbox(u8"Приоритет крупных объектов и вытеснение мелких при лимите", bPrio) then
                cfg.prioritizeLarge = bPrio[0]
                saveSettings()
                forceStreamTick = true
            end

            local bCol = imgui.new.bool(cfg.disableFarCollision)
            if imgui.Checkbox(u8"Отключать физическую коллизию у дальних объектов", bCol) then
                cfg.disableFarCollision = bCol[0]
                saveSettings()
            end

            local bUpd = imgui.new.bool(cfg.autoUpdate)
            if imgui.Checkbox(u8"Автообновление скрипта", bUpd) then
                cfg.autoUpdate = bUpd[0]
                saveSettings()
            end
            imgui.SameLine()
            if imgui.Button(u8"Проверить обновление") then
                checkUpdates(true)
            end

            imgui.Spacing()
            imgui.Separator()
            imgui.Spacing()

            local dbPath = getServerFilePath(currentServerKey)
            local dbSize = file_exists(dbPath) and (lfs.attributes(dbPath, "size") or 0) or 0
            local sizeText = dbSize < 1024 and string.format("%d B", dbSize)
                or (dbSize < 1048576 and string.format("%.2f KB", dbSize / 1024.0) or string.format("%.2f MB", dbSize / 1048576.0))

            local btnWidth = 100
            local currentY = imgui.GetCursorPosY()
            imgui.AlignTextToFramePadding()
            imgui.TextColored(imgui.ImVec4(0.6, 0.6, 0.6, 1.0), u8"Размер базы данных: " .. sizeText)

            imgui.SameLine()
            local availRight = imgui.GetContentRegionAvail().x
            if availRight > btnWidth then
                imgui.SetCursorPosX(imgui.GetCursorPosX() + availRight - btnWidth)
            end
            imgui.SetCursorPosY(currentY)
            if imgui.Button(u8"Закрыть", imgui.ImVec2(btnWidth, 0)) then
                UI.windowState[0] = false
            end

            imgui.End()
        end

        imgui.PopStyleVar(5)
        imgui.PopStyleColor(16)
    end
)

function main()
    if not isSampLoaded() or not isSampfuncsLoaded() then return end
    while not isSampAvailable() do wait(100) end

    if file_exists(settingsFile) then
        local loaded = load_json(settingsFile)
        if type(loaded) == "table" then
            for k, v in pairs(loaded) do
                if cfg[k] ~= nil then cfg[k] = v end
            end
        end
    else
        saveSettings()
    end

    UI.maxObjBuf[0] = cfg.maxLocalObjects

    sampRegisterChatCommand("chunky", function()
        UI.windowState[0] = not UI.windowState[0]
    end)

    checkUpdates(false)

    local wasSpawned = false
    local lastStreamTick = os.clock()
    local lastFrameClock = os.clock()

    while true do
        wait(0)
        local now = os.clock()
        local dt = math.min(0.25, math.max(0.001, now - lastFrameClock))
        lastFrameClock = now

        local speed = math.max(25, cfg.spawnSpeed or 300)
        spawnBudget = math.min(speed * 0.25, spawnBudget + speed * dt)

        local ip, port = sampGetCurrentServerAddress()
        if ip and port and ip ~= "" then
            local sanitized = (ip .. "_" .. tostring(port)):gsub("[^%w%_]", "_")
            if sanitized ~= currentServerKey then
                saveServerDatabase(false)
                currentServerKey = sanitized
                currentServerDisplay = string.format("%s:%s", ip, tostring(port))
                loadServerDatabase(currentServerKey)
            end
        end

        local spawnedNow = sampIsLocalPlayerSpawned()
        if spawnedNow and not wasSpawned then
            lastSpawnedClock = now
            lastTeleportTime = now
            scanExistingServerObjects()
        end
        wasSpawned = spawnedNow

        if spawnedNow and #deferredMatQueue > 0 then
            processDeferredMatQueue()
        end

        if (forceStreamTick and (now - lastStreamTick >= 0.08)) or (now - lastStreamTick >= 0.20) then
            forceStreamTick = false
            lastStreamTick = now
            processStreamingTick()
        end

        if cfg.enabled and spawnedNow then
            processSpawnQueue(now)
        end

        if dbDirty and (now - lastSaveTime >= 60.0) and (now - lastServerCreateTime >= 2.0) then
            saveServerDatabase(false)
        end
    end
end