/*
//=============================================================================================================
//
//		Name        : 	JOIDE Framework (xGovern)
//		Author      : 	Joe K. Kim (J.K.K.)
//		Site		:	xgovern.com, joide.com
//		Version     : 	0.0.0
//		
//		!!! Proprietary !!!
//
//		© 2018 xGovern Inc., all rights reserved.
//		Unauthorized copying of this file, via any medium is strictly prohibited.
//		Written by Joe K. Kim <jkk@xgovern.com>
//
//=============================================================================================================
*/
var is_nodeJS_master, is_nodeJS, is_worker;
is_nodeJS = (new Function("try{return this===global;}catch(e){return false;}"))();
if(is_nodeJS){try{is_worker=require?false:true;}catch(e){is_worker = true;}}
else{is_worker = (new Function("try{document}catch(e){return true;}"))();}
is_nodeJS_master = (is_nodeJS && !is_worker);

var JOIDE = (function(){
	
	var joide = {};
	
	var s3, db, dbt, rodb, rodbt, s3, wss, server, code_db;
	var terminate_signal = false;
	var SG = server, WS = {}, REQ = {};
	var server = {}, server_peers = {};
	var sb = {};//struct base
	var structbase = {};
	var struct_typemap = {};
	var ip_visit_reg = {};
	var client_by_uid = {};
	var clients = [];
	var alive_clients = [];
	var calls = {};
	var data_subs = {code:{}};
	var codebase_allowed_emails = ['jkk@xgovern.com','kimjo625@gmail.com','eduhash.demo@gmail.com','onhpe@naver.com','kshrabbit@gmail.com'];
	var codebase_authorized_peer_domains = ['eduhash.app'];

	var structinst; //instantiation
	var skeletonize; //data skeletonize for handling

	//Independent Functions
	var time = function(){return Math.floor((new Date).getTime()/1000);}
	var mtime = function(){return (new Date).getTime();}
	var fulltime = function(s,ns){
		var hrt = (s === undefined && ns === undefined) ? process.hrtime() : [s,ns];
		if(!hrt[0]) hrt[0] = time(); if(!hrt[1]) hrt[1] = process.hrtime()[1];
		var t = new Date(), ms = t.getTime();
			hrt[1] = hrt[1] - ms*1000000; if(hrt[1] < 0) hrt[1] = Math.abs(1000000000 - hrt[1]);
		return {
			d:{//date
				y:t.getFullYear(),
				m:t.getMonth(),
				d:t.getDate(),
				a:t.getDay(),//Day
			},
			t:{//time
				h:t.getHours(),
				m:t.getMinutes(),
				s:t.getSeconds(),
			},
			o:t.getTimezoneOffset(),//timezone offset
			h:{//high resolution
				m:t.getMilliseconds(),
				u:Math.floor(hrt[1]/1000)%1000,
				n:hrt[1]%1000,
			},
			ts:Math.floor(ms/1000),//timestamp in seconds
			ns:hrt[1],//additional nanoseconds
		};
	}
	var portable_error = function(e,c){
		if(!e) e = new Error; if(!c) c = "";
		if(typeof e === 'string') e = new Error(e);
		return {message:e.message, stack:e.stack, name:e.name, code:e.code?e.code:c};
	}
	var e_add = function(e1,e2){
		if(!e2) return e1; if(!e1 && e2) return e2;
		e1 = portable_error(e1);
		e2 = portable_error(e2);
		e1.stack = e2.stack + "\n" + e1.stack;
		return e1;
	}
	var e_merge = function(e1,e2,param){
		if(!e1 && !e2) return new Error('Unknown Error');
		if(!e1) return e2; if(!e2) return e1;
		e1.name = e2.name;
		e1.type = e2.type;
		e1.code = e2.code;
		e1.stack = e1.stack + "\n\t" + e2.stack;
		if(param){
			try{
				e1.stack = e1.stack + "\n\t" + JSON.stringify(param);
			}
			catch(e){console.log(e);}
		}
		return e1;
	}

	const pako = require('pako');
	const util = require('util');
	const obj_const = Object.prototype.constructor;
	const arr_const = Array.prototype.constructor;
	var is_newable = function(a){return (a && a.newable);}
	var is_object = function(a){return (a && a.constructor === obj_const);}
	var is_array = function(a){return (a && a.constructor === arr_const);}
	var is_string = function(a){return (a && typeof a === 'string');}
	var is_function = function(a){return (a && typeof a === 'function');}
	var sort_object_keys = function(obj){
		//TODO: what comparison & collation is the sort function using?
		return Object.keys(obj).sort().reduce(function(result,key){result[key] = obj[key]; return result;}, {});
	}
	var obj_neat_assign, arr_neat_assign;
	obj_neat_assign = function(a,b){
		var i,c,d;
		if(arguments.length === 2){
			if(!a || !b) throw new Error('Supplied argument is not an object');
			if(a.constructor !== obj_const || b.constructor !== obj_const) throw new Error('Supplied argument is not an object');
			for(var p in b){
				c = a[p];
				d = b[p];
				if(c === undefined || c === null){
					if(d && d.constructor === obj_const) a[p] = obj_neat_assign({},d);
					else if(d && d.constructor === arr_const) a[p] = arr_neat_assign([],d);
					else a[p] = d;
				}
				else if(c.constructor === obj_const && d !== null && d.constructor === obj_const){
					a[p] = obj_neat_assign({},c,d);
				}
				else if(c.constructor === arr_const && d !== null && d.constructor === arr_const){
					a[p] = arr_neat_assign([],c,d);
				}
				else{
					if(d && d.constructor === obj_const) a[p] = obj_neat_assign({},d);
					else if(d && d.constructor === arr_const) a[p] = arr_neat_assign([],d);
					else a[p] = d;
				}
			}
			a = sort_object_keys(a);
			return a;
		}
		else if(arguments.length >= 3){
			if(!a || a.constructor !== obj_const) throw new Error('Supplied argument is not an object');
			var arglen = arguments.length;
			for(i = 1; i < arglen; ++i){
				c = arguments[i];
				if(!c || c.constructor !== obj_const) throw new Error('Supplied argument is not an object');
				if(c !== undefined && c !== null && c.constructor === obj_const) obj_neat_assign(a,c);
			}
			a = sort_object_keys(a);
			return a;
		}
		else{
			a = sort_object_keys(a);
			return a;
		}
	}
	arr_neat_assign = function(a,b){
		var i,c,d;
		if(arguments.length === 2){
			if(!a || !b) throw new Error('Supplied argument is not an array');
			if(a.constructor !== arr_const || b.constructor !== arr_const) throw new Error('Supplied argument is not an array');
			var blen = b.length;
			for(i = 0; i < blen; ++i){
				c = a[i]; d = b[i];
				if(c === undefined || c === null){
					if(d && d.constructor === obj_const) a[i] = obj_neat_assign({},d);
					else if(d && d.constructor === arr_const) a[i] = arr_neat_assign([],d);
					else a[i] = d;
				}
				else if(c.constructor === obj_const && d !== null && d.constructor === obj_const){
					a[i] = obj_neat_assign({},c,d);
				}
				else if(c.constructor === arr_const && d !== null && d.constructor === arr_const){
					a[i] = arr_neat_assign([],c,d);
				}
				else{
					if(d && d.constructor === obj_const) a[i] = obj_neat_assign({},d);
					else if(d && d.constructor === arr_const) a[i] = arr_neat_assign([],d);
					else a[i] = d;
				}
			}
			return a;
		}
		else if(arguments.length >= 3){
			if(!a || a.constructor !== arr_const) throw new Error('Supplied argument is not an array');
			var arglen = arguments.length;
			for(i = 1; i < arglen; ++i){
				c = arguments[i];
				if(!c || c.constructor !== arr_const) throw new Error('Supplied argument is not an array');
				if(c !== undefined && c !== null && c.constructor === arr_const) arr_neat_assign(a,c);
			}
			return a;
		}
		else{
			return a;
		}
	}
	var verbose_stack_top = function(e){
		try{
			var split = e.stack.split("\n");
			var loc = split[1].split("at ")[1].split(" (");
			var func = loc[0].split("."); func = func[func.length-1];
			var src = "(at "+loc[1];
			return "[verbose; '"+ func + "']: " + e.message + " " + src;
		}
		catch(e){
			return "[Verbose: unknown_func]: " + e.message + " (at ?)";
		}
	}
	var if_verbose = function(options,e){
		if(e && options && options.verbose){
			if(is_string(e)) e = new Error(e);
			//options.verbose_handler ? options.verbose_handler(e) : console.log(e);
			options.verbose_handler ? options.verbose_handler(e) : (options.verbose_max ? console.log(e) : console.log(verbose_stack_top(e)));
			is_array(options.verbose_log) ? options.verbose_log.push(e) : null;
			is_array(options.verbose_logs) ? options.verbose_logs.push(e) : null;
		}
	}
	var progress_update = function(data,options){
		if(options && options.onprogress && !options._resolved) options.onprogress(data);
	}
	var resolve = function(data,options,e,do_throw){
		if(e && options && options.verbose){
			options.verbose_handler ? options.verbose_handler(e) : console.log(e)
			is_array(options.verbose_log) ? options.verbose_log.push(e) : null;
		}
		if(!e) e = new Error("Unspecified Error/Resolution.");
		if(do_throw){
			if(options && options.callback && !options._resolved){
				(data !== false && data !== null && data !== undefined) ? options.callback(null,data) : options.callback(e,data);
				options._resolved = function(){};
			}
			throw e;
		}
		else{
			if(options && options.callback && !options._resolved){
				(data !== false && data !== null && data !== undefined) ? options.callback(null,data) : options.callback(e,data);
				options._resolved = function(){};
			}
			return data;
		}
	}
	var sanitize_empty_string = function(a,options){
		if(!options) options = {};
		if(options.copy) a = JSON.parse(JSON.stringify(a));
		if(is_array(a)){
			var alen = a.length;
			for(var i = 0; i < alen; ++i){
				var b = a[i];
				if(b === ''){
					a[i] = null;
				}
				else if(is_array(b) || is_object(b)){
					sanitize_empty_string(b);
				}
			}
		}
		else if(is_object(a)){
			for(var p in a){
				var b = a[p];
				if(b === ''){
					a[p] = null;
				}
				else if(is_array(b) || is_object(b)){
					sanitize_empty_string(b);
				}
			}
		}
		return a;
	}
	var cleanse_circular = function(target,cache){
		if(!cache) cache = [];
		if(is_object(target)){
			return util.inspect(target);
		}
		else if(is_array(target)){
			for(var i = 0; i < target.length; ++i){
				var a = target[i];
				if(cache.indexOf(a) === -1){
					cache.push(a);
					target[i] = cleanse_circular(a,cache);
				}
				else{
					target[i] = '[Circular]';
				}
			}
			return target;
		}
		else{
			return target;
		}
	}
	var obj_copy = function(a){return JSON.parse(JSON.stringify(a));}
	var ripcut_str, ripcut_ver, ripcut_num;
	ripcut_str = function(v){
		if(typeof v === 'string') return v;
		if(typeof v === 'number') v = ripcut_ver(v);
		if(v.r == 0 && v.i == 0 && v.p == 0 && v.c == 0 && v.u == 0 && v.t == 0) return '0';
		return v.r+'.'+v.i+'.'+v.p+'.'+v.c+'.'+v.u+'.'+v.t;
	}
	ripcut_ver = function(v){
		if(typeof v === 'number'){
			//TODO
		}
		v = v+'';
		if(v.indexOf('.') === 0) return {r:0,i:0,p:0,c:0,u:0,t:0};
		v = v.split('.');
		while(v.length < 6) v.unshift(0);
		while(v.length > 6) v.pop(0);
		for(var i = 0; i < 6; ++i) v[i] = parseInt(v[i]);
		for(var i = 0; i < 6; ++i) if(isNaN(v[i])) v[i] = 0;
		return {r:v[0],i:v[1],p:v[2],c:v[3],u:v[4],t:v[5]};
	}
	ripcut_num = function(v){
		if(typeof v === 'string') v = ripcut_ver(v);
		var n = v.t, mult = 100000;
		n += v.u * mult; mult *= 100; 
		n += v.c * mult; mult *= 100; 
		n += v.p * mult; mult *= 100;
		n += v.i * mult; mult *= 100;
		n += v.r * mult;
		return n;
	}
	
	
	try{if(is_nodeJS_master && module) module.exports = joide;}
	catch(e){}
	
	Object.freeze(joide);
    return joide;
    
})();