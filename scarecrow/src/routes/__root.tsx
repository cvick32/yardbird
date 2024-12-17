import {
  Link,
  Outlet,
  createRootRouteWithContext,
} from "@tanstack/react-router";
import { QueryClient } from "@tanstack/react-query";
import { AuthContext } from "../AuthProvider";

interface RouterContext {
  queryClient: QueryClient;
  auth: AuthContext;
}

export const Route = createRootRouteWithContext<RouterContext>()({
  component: RootComponent,
});

function RootComponent() {
  return (
    <>
      <div className="flex gap-2 bg-white p-2">
        <div className="grow">
          <Link to="/" className="hover:underline [&.active]:font-bold">
            Index
          </Link>
        </div>
        <div>
          <a
            href="https://github.com/cvick32/yardbird"
            className="hover:underline [&.active]:font-bold"
          >
            Repo
          </a>
        </div>
        <div>
          <Link to="/logout" className="hover:underline [&.active]:font-bold">
            Log Out
          </Link>
        </div>
      </div>
      <hr />
      <div className="m-2">
        <Outlet />
      </div>
    </>
  );
}
